-- Prove2me | Theorems.Thm_MinimaxWass_Smooth_lemma_2
-- name    : MinimaxWass.Smooth.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:47.435983+00:00
-- url     : https://prove2.me/theorems/374a6a33-f56a-4cb9-ac0f-98dd51ee607e
-- title:
--   Lemma 2, p. 6 — under Assumptions 1, 2, 4 the optimal dual multiplier satisfies λ̃ ≤ C₀2^{p−1}(1 + (diam(𝒵)/ϱ)^p)
-- statement:
--   Let $\mathcal Z$ be a bounded Polish metric space (Assumption 1), $p\ge1$, $\varrho>0$, and let $\mathcal F$ be a class of upper semicontinuous functions with $0\le f\le M$ (Assumption 2). Suppose (Assumption 4) there are $f_0\in\mathcal F$, $z_0\in\mathcal Z$ and $C_0\ge0$ with $f_0(z)\le C_0\,d^p_{\mathcal Z}(z,z_0)$ for all $z$.
--
--   Fix a Borel probability measure $Q$. Let $\tilde f\in\mathcal F$ minimise $R_{\varrho,p}(Q,\cdot)$ over $\mathcal F$, and let $\tilde\lambda\ge0$ minimise $\lambda\mapsto\lambda\varrho^p+\mathbf E_Q[\varphi_{\lambda,\tilde f}(Z)]$ over $\lambda\ge0$. Then
--
--   $$\tilde\lambda\le C_0\,2^{p-1}\Bigl(1+\Bigl(\frac{\mathrm{diam}(\mathcal Z)}{\varrho}\Bigr)^p\Bigr).$$
--
--   The lemma confines the optimal dual multiplier of the local minimax problem to a fixed compact interval that depends only on $C_0$, $p$, $\varrho$ and $\mathrm{diam}(\mathcal Z)$, not on $Q$; this is what makes the dual class $\Phi$ of the excess-risk proof a bounded-complexity class.
--
--   **Formalization Note** The paper's "$\tilde f:=\arg\min$" and "$\tilde\lambda:=\arg\min$" are given as hypotheses: $\tilde f\in\mathcal F$ with $R_{\varrho,p}(Q,\tilde f)\le R_{\varrho,p}(Q,f)$ for all $f\in\mathcal F$, and $\tilde\lambda\ge0$ minimising the dual objective. The paper's $Q\in\mathcal P_p(\mathcal Z)$ is automatic on a bounded space. Powers with real exponent are real powers of nonnegative bases.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 6, Lemma 2; Assumption 4, p. 6; proof Appendix C.4, pp. 15–16

import Mathlib
import Definitions.Def_MinimaxWass_Smooth_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace MinimaxWass.Smooth

/-- Lemma 2, p. 6: the optimal dual multiplier of the minimiser is at most
`C₀ 2^{p−1} (1 + (diam(𝒵)/ϱ)^p)`. -/
theorem lemma_2 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbdd : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    {ℱ : Set (𝒵 → ℝ)} {M : ℝ}
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f) (hbddF : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    {f₀ : 𝒵 → ℝ} (hf₀ : f₀ ∈ ℱ) {z₀ : 𝒵} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hf₀_le : ∀ z, f₀ z ≤ C₀ * dist z z₀ ^ p)
    (Q : ProbabilityMeasure 𝒵) {ftil : 𝒵 → ℝ} (hftil_mem : ftil ∈ ℱ)
    (hftil_min : ∀ f ∈ ℱ, MinimaxWass.DataDep.localRisk p ϱ Q ftil ≤ MinimaxWass.DataDep.localRisk p ϱ Q f)
    {lamtil : ℝ} (hlamtil_nonneg : 0 ≤ lamtil)
    (hlamtil_min : ∀ lam : ℝ, 0 ≤ lam →
      dualObjective p ϱ Q ftil lamtil ≤ dualObjective p ϱ Q ftil lam) :
    lamtil ≤ C₀ * 2 ^ (p - 1) * (1 + (Metric.diam (Set.univ : Set 𝒵) / ϱ) ^ p) := by sorry

end MinimaxWass.Smooth
