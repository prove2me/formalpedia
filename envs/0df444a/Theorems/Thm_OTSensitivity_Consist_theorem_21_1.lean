-- Prove2me | Theorems.Thm_OTSensitivity_Consist_theorem_21_1
-- name    : OTSensitivity.Consist.theorem_21_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:17.649358+00:00
-- url     : https://prove2.me/theorems/e2ce87d3-2b8f-4dbe-bf5d-e7de52b0fccb
-- title:
--   Theorem 21 (1), (78), p. 39 — for finite $\mathsf X$, $\xi^K(Y^N,X^N)\to\xi^K(Y,X)$
-- statement:
--   Let $\mathsf X=\{x^1,\dots,x^H\}$ be finite (discrete topology, $\mathcal F=2^{\mathsf X}$) and $\mathsf Y$ Polish. Let $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ be continuous with $k(y,y')=0\iff y=y'$, and let $a_1,a_2:\mathsf Y\to[0,\infty)$ be continuous with $k(y,y')\le a_1(y)+a_2(y')$. Let $\pi^N$ and $\pi$ be probability measures on $\mathsf X\times\mathsf Y$ (the joint laws of $(X^N,Y^N)$ and $(X,Y)$) with $\pi^N\to\pi$ weakly, and assume (73): with $a=a_1+a_2$ and $\nu^N$, $\nu$ the second marginals,
--   $$\lim_{N\to\infty}\int a\,d\nu^N=\int a\,d\nu<\infty.$$
--   Then, for every choice of versions of the conditional distributions,
--   $$\lim_{N\to\infty}\xi^K(Y^N,X^N)=\xi^K(Y,X).$$
--
--   This is the consistency of the OT-based sensitivity measure for a finite-valued input: any sequence of joint laws converging weakly with converging $a$-moments, in particular empirical laws, yields convergent values of $\xi^K$.
--
--   **Formalization Note** $\mathsf Y$ is Polish (the paper's support in $\mathbb R^{n_Y}$ is such a space). The statement is made on joint laws: $\Omega=\mathsf X\times\mathsf Y$, $\mathbb P=\pi^N$ (resp. $\pi$), coordinate projections. Weak convergence is Mathlib's topology on probability measures. Values are in $[0,+\infty]$; $K$ is `RWPI.SqrtLasso.transportCost`; the conditional laws are arbitrary kernels satisfying the characterizing predicate. The page prints $\xi^K(X,Y)$ in (78); the paper's convention and the proof's (80) compute $\xi^K(Y,X)$, which is what is stated. The paper assumes (73) "when k is not bounded"; it is assumed here unconditionally, which loses nothing since a bounded $k$ satisfies the separate-cost bound and (73) with constant $a_1=a_2=\tfrac12\sup k$.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Theorem 21 (1), (78), p. 39; setting (73)–(74), p. 38; bounded separate costs, p. 4; §3.1, p. 9

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_Consist_Setting
import Definitions.Def_OTSensitivity_Consist_Estimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.Consist

/-- Theorem 21 (1), (78), p. 39. If `𝒳` is finite (with `𝓕 = 2^𝒳`), the joint laws `π^N` converge
weakly to `π`, the cost satisfies the standing assumption and the separate-cost bound, and (73)
holds, then `ξ^K(Y^N, X^N) → ξ^K(Y, X)`, for every choice of versions of the conditional
distributions. (The page prints `ξ^K(X, Y)`; the proof's (80) computes `ξ^K(Y, X)`.) -/
theorem theorem_21_1 {𝒳 𝒴 : Type*}
    [Fintype 𝒳] [TopologicalSpace 𝒳] [DiscreteTopology 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (a₁ a₂ : 𝒴 → ℝ≥0) (ha : IsSeparateCostBound k a₁ a₂)
    (πs : ℕ → ProbabilityMeasure (𝒳 × 𝒴)) (π : ProbabilityMeasure (𝒳 × 𝒴))
    (hπ : Tendsto πs atTop (𝓝 π))
    (h73 : MomentConvergence a₁ a₂ (fun N => (πs N : Measure (𝒳 × 𝒴))) (π : Measure (𝒳 × 𝒴)))
    (κs : ℕ → Kernel 𝒳 𝒴)
    (hκs : ∀ N, IsCondDistrib (πs N : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd ‹MeasurableSpace 𝒳›
      (κs N))
    (κ : Kernel 𝒳 𝒴)
    (hκ : IsCondDistrib (π : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd ‹MeasurableSpace 𝒳› κ) :
    Tendsto (fun N => xi k (πs N : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd (κs N)) atTop
      (𝓝 (xi k (π : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd κ)) := by sorry

end OTSensitivity.Consist
