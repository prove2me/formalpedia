-- Prove2me | Theorems.Thm_MHSpectralGap_RWM_halfspace_flow
-- name    : MHSpectralGap.RWM.halfspace_flow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:14:54.164832+00:00
-- url     : https://prove2.me/theorems/74999d3a-2ca1-4aa9-9915-f7eced1a2d11
-- title:
--   Proof of Theorem 2.17 (2), p. 17 — A = {x₁ ≥ 0} has γ_m(A) = 1/2 and ∫_A Q(x, Aᶜ)γ_m(dx) ≤ c√(δ/(δ+1)), c independent of m, δ
-- statement:
--   Consider the random walk Metropolis proposal on $\mathbb R^m$ for the Gaussian target $\gamma_m$ of (2.5): from $x$ propose $y=x+\sqrt{2\delta}\,\xi$ with $\xi\sim\gamma_m$; write $Q(x,\cdot)$ for its law. Let $A=\{x\in\mathbb R^m: x_1\ge 0\}$. There is a constant $c$, independent of $m$ and $\delta$, such that for every $m\ge1$ and every $\delta>0$,
--
--   $$
--   \gamma_m(A)=\tfrac12\qquad\text{and}\qquad\int_A Q(x,A^c)\,\gamma_m(dx)\;\le\;c\,\sqrt{\frac{\delta}{\delta+1}} .
--   $$
--
--   Since a Metropolis–Hastings move out of $A$ requires a proposal out of $A$, the conductance of the RWM kernel is at most $2c\sqrt{\delta/(\delta+1)}$, and with $\delta_m=s\,m^{-a}$ this gives Theorem 2.17 (2) through Cheeger's inequality.
--
--   **Formalization Note** The paper's displays at this point are garbled (they read "$\mathsf C/2\le\dots$", use $n$ for $m$ and $n!$ for $m!$, and invoke Fernique's theorem for what is a one-dimensional Gaussian integral); this item states what the surrounding sentences and the final bound $\mathsf C\le K\sqrt{2\pi\delta/(\delta+1)}$ support, namely the half-space mass and the bound on the proposal flow out of $A$. The paper's coordinate $x_1$ is the Lean coordinate `0 : Fin m`.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 17, proof of Theorem 2.17 (2), the paragraph "For the second part of the poof we use α(x, y) ≤ 1 and A = {x ∈ R^n | x_1 ≥ 0}" and the display "C ≤ K ∫ … ≤ K√(2πδ/(δ+1)) ≤ K̃ m^{−a/2}"

import Mathlib
import Definitions.Def_MHSpectralGap_RWM_MHKernel
import Definitions.Def_MHSpectralGap_RWM_L2Gap
import Definitions.Def_MHSpectralGap_RWM_Conductance
import Definitions.Def_MHSpectralGap_RWM_RWMKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- Proof of Theorem 2.17 (2), p. 17: the half-space `A = {x | x₁ ≥ 0}` has `γ_m(A) = 1/2`,
and the probability flow of the RWM proposal out of `A` satisfies
`∫_A Q(x, Aᶜ) γ_m(dx) ≤ c √(δ / (δ + 1))` with `c` independent of `m` and `δ`. -/
theorem halfspace_flow :
    ∃ c : ℝ, ∀ (m : ℕ) (hm : 1 ≤ m) (δ : ℝ), 0 < δ →
      gammaM m {x | 0 ≤ x ⟨0, hm⟩} = 1 / 2 ∧
      ∫⁻ x in {x | 0 ≤ x ⟨0, hm⟩}, rwmProposal m δ x {x | 0 ≤ x ⟨0, hm⟩}ᶜ ∂(gammaM m) ≤
        ENNReal.ofReal (c * Real.sqrt (δ / (δ + 1))) := by sorry

end MHSpectralGap.RWM
