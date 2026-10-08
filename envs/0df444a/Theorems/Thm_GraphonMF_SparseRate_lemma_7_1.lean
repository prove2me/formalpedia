-- Prove2me | Theorems.Thm_GraphonMF_SparseRate_lemma_7_1
-- name    : GraphonMF.SparseRate.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:48.202169+00:00
-- url     : https://prove2.me/theorems/10a4b5ee-59d7-4558-aa95-45a35f4e142a
-- title:
--   Lemma 7.1, p. 3610 — sup over n and i of 𝔼‖Xⁿ_i − X_{i/n}‖^k_{*,T} is finite for every k (under Condition 4.3)
-- statement:
--   Fix the setting of the mission: the continuum noise, coefficients $b,\sigma$ and sparsity $\beta_n$ satisfying Condition 4.1, a graphon $G$, edge variables $\xi^n_{ij}$ satisfying Condition 4.3, and a solution $X=(X_u)_{u\in I}$ of the limit system (4.2). Then for every $k\in\mathbb N$ there is a constant $C_k<\infty$ such that, for every $n$, every solution $(X^n_i)_{i\le n}$ of the not-so-dense system (4.1) and every $i\in\{1,\dots,n\}$,
--   $$\mathbb E\big\|X^n_i-X_{i/n}\big\|_{*,T}^k\le C_k,\qquad\text{that is,}\qquad \sup_{n\in\mathbb N}\max_{i=1,\dots,n}\mathbb E\big\|X^n_i-X_{i/n}\big\|_{*,T}^k<\infty .$$
--
--   The bound controls all moments of the coupling error uniformly in the population size; Hölder's inequality turns it into the error terms $\kappa(q)/(n\beta_n)^{1/q}$ of (7.10) and (7.15).
--
--   **Formalization Note** The paper states the lemma under "either Condition 4.2 or Condition 4.3"; this mission states the Condition 4.3 case, the one Theorem 4.2 uses. The same lemma under Condition 4.2 is a milestone of the companion mission IV. The moment is a lower Lebesgue integral in $[0,\infty]$ of $\|\cdot\|_{*,T}^k$, the norm of $\mathcal C_d$.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3610, Lemma 7.1

import Mathlib
import Definitions.Def_GraphonMF_SparseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.SparseRate

/-- Lemma 7.1 (p. 3610), under Condition 4.3: uniform moments of the coupling error,
`sup_n max_i 𝔼‖Xⁿ_i − X_{i/n}‖^k_{*,T} < ∞` for every `k ∈ ℕ`. -/
theorem lemma_7_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B)
    {b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {β : ℕ → ℝ} (h41 : Cond41 μ0 b σ β) {G : I → I → ℝ} (hG : GraphonMF.DenseRate.IsGraphon G)
    {ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ} (h43 : Cond43 P X0 B ξ β G)
    {X : I → ℝ≥0 → Ω → Fin d → ℝ} (hX : IsGraphonSolution42 P hN T b σ G X) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → Fin d → ℝ),
      IsParticleSolution41 P hN h43.meas T b σ β n Xn → ∀ i : Fin n,
        ∫⁻ ω, ‖GraphonMF.DenseRate.pathOf T (Xn i) ω - GraphonMF.DenseRate.pathOf T (X (GraphonMF.DenseRate.lab n i)) ω‖ₑ ^ k ∂P ≤ ENNReal.ofReal C := by sorry

end GraphonMF.SparseRate
