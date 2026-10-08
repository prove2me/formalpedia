-- Prove2me | Theorems.Thm_GenEmpLik_Consistency_corollary_1
-- name    : GenEmpLik.Consistency.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:14:10.199007+00:00
-- url     : https://prove2.me/theorems/7fc718a2-c7d1-41c9-a6a3-913ba9081574
-- title:
--   Corollary 1 — robust optimal values and solution sets over f-divergence balls are consistent
-- statement:
--   Let $\xi_1,\xi_2,\dots$ be i.i.d. random elements of a separable metric space $\Xi$ with law $P_0$ and let $\widehat P_n$ be the empirical distribution of the first $n$. Let $\mathcal X\subset\mathbb R^d$ be nonempty and compact, let $\ell:\mathbb R^d\times\Xi\to\mathbb R$ be lower semicontinuous on $\mathcal X\times\Xi$, with $\ell(x;\cdot)$ measurable for every $x\in\mathcal X$ and $\ell(\cdot;\xi)$ continuous on $\mathcal X$ for every $\xi$. Let $f$ satisfy Assumption A, $\rho\ge0$, and let Assumption E hold. Define the robust and population objectives
--
--   $$
--   \widehat F_n(x)=\sup_{P\ll\widehat P_n}\Big\{E_P[\ell(x;\xi)] : D_f(P\|\widehat P_n)\le\frac{\rho}{n}\Big\},\qquad F(x)=E_{P_0}[\ell(x;\xi)],
--   $$
--
--   and the solution sets $S^\star_{\widehat P_n}=\operatorname{argmin}_{x\in\mathcal X}\widehat F_n(x)$ and $S^\star_{P_0}=\operatorname{argmin}_{x\in\mathcal X}F(x)$. Then, in outer probability,
--
--   $$
--   \inf_{x\in\mathcal X}\widehat F_n(x)-\inf_{x\in\mathcal X}F(x)\ \xrightarrow{\ P^*\ }\ 0
--   \qquad\text{and}\qquad
--   d_\subset\big(S^\star_{\widehat P_n},S^\star_{P_0}\big)\ \xrightarrow{\ P^*\ }\ 0 .
--   $$
--
--   So the optimal value of the distributionally robust problem is a consistent estimate of the population optimal value, and its minimisers eventually lie arbitrarily close to the population minimisers: robustness costs nothing in consistency under these conditions.
--
--   **Formalization Note** Convergence in outer probability is stated as: for every $\delta>0$, $\mu^*\{\omega : \delta<|\cdot|\}\to0$, where $\mu\,s$ for an arbitrary set $s$ is Mathlib's outer measure (no measurability assumed). $d_\subset$ takes values in $[0,\infty]$ and the second event is $\{\delta<d_\subset\}$. Samples are 0-based, $P_0$ is the law of $\xi_0$, and $\widehat F_n(x)$ is `robustMean f ρ (ℓ(x;ξ_0),…,ℓ(x;ξ_{n-1}))`. Nonemptiness of $\mathcal X$ is the paper's standing assumption (p. 1); nonemptiness of the solution sets is not assumed.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 17, Corollary 1 (with (23), p. 16, and (6), p. 5)

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Consistency_AssumptionE
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_GenEmpLik_Consistency_argminSet
import Definitions.Def_GenEmpLik_Consistency_inclDist

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace GenEmpLik.Consistency

/-- Corollary 1 (arXiv:1610.03425v3, p. 17). Let `ξ₀, ξ₁, …` be i.i.d. with law `P₀`, let `f`
satisfy Assumption A, `ρ ≥ 0`, let `X ⊂ ℝ^d` be nonempty and compact, and let `Ξ` be a
separable metric space. Let `ℓ` be lower semicontinuous on `X × Ξ`, `ℓ(·; ξ)` continuous on
`X` for every `ξ`, `ℓ(x; ·)` measurable for `x ∈ X`, and let Assumption E hold. With
`F̂_n(x) = sup { E_P[ℓ(x; ξ)] : P ≪ P̂_n, D_f(P ‖ P̂_n) ≤ ρ/n }` and `F(x) = E_{P₀}[ℓ(x; ξ)]`,
`inf_X F̂_n − inf_X F → 0` and `d_⊂(argmin_X F̂_n, argmin_X F) → 0` in outer probability. -/
theorem corollary_1 {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MetricSpace Ξ]
    [SecondCountableTopology Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
    (f : ℝ → EReal) (hf : GenEmpLik.Coverage.AssumptionA f) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ξ : ℕ → Ω → Ξ) (hξm : ∀ i, Measurable (ξ i)) (hξind : iIndepFun ξ μ)
    (hξid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X) (hXne : X.Nonempty)
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (hℓm : ∀ x ∈ X, Measurable (ℓ x))
    (hℓlsc : LowerSemicontinuous (fun xs : X × Ξ => ℓ xs.1 xs.2))
    (hcont : ∀ s, ContinuousOn (fun x => ℓ x s) X)
    (hE : AssumptionE (μ.map (ξ 0)) X ℓ) :
    (∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => μ {ω |
        δ < |(⨅ x : X, GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => ℓ x (ξ i ω)))
          - ⨅ x : X, ∫ s, ℓ x s ∂(μ.map (ξ 0))|}) atTop (𝓝 0)) ∧
    (∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => μ {ω |
        ENNReal.ofReal δ < inclDist
          (argminSet X (fun x => GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => ℓ x (ξ i ω))))
          (argminSet X (fun x => ∫ s, ℓ x s ∂(μ.map (ξ 0))))}) atTop (𝓝 0)) := by sorry

end GenEmpLik.Consistency
