-- Prove2me | Theorems.Thm_MHSpectralGap_RWM_theorem_2_17_ii
-- name    : MHSpectralGap.RWM.theorem_2_17_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:17:35.369613+00:00
-- url     : https://prove2.me/theorems/75695588-b04f-46b7-8c4b-72ae63e0cbb7
-- title:
--   Theorem 2.17 (2), p. 16 — for δ_m = s m^{−a}, a ≥ 1, the L²-spectral gap of RWM satisfies 1 − β_m ≤ K(a) m^{−a/2}
-- statement:
--   For $m\ge1$ let $\gamma_m$ be the Gaussian measure (2.5) on $\mathbb R^m$ (independent coordinates $x_i\sim\mathcal N(0,1/i^2)$) and let $P_m$ be the random walk Metropolis kernel targeting $\gamma_m$ with step size $\delta_m=s\,m^{-a}$, where $s>0$ is fixed. Let $\beta_m=\|P_m\|_{L^2_0\to L^2_0}$ (Definition 2.7 with $\mu=\gamma_m$), so that $1-\beta_m$ is the $L^2_{\gamma_m}$-spectral gap of $P_m$. If $a\ge1$, there is a constant $K$, depending on $a$ and $s$ but not on $m$, such that for all $m\ge 1$
--
--   $$
--   1-\beta_m\;\le\;K\,m^{-a/2}.
--   $$
--
--   When the step size shrinks at least as fast as $1/m$, the chain is slow because its proposals are small, and the gap decays at least like the square root of the step size.
--
--   **Formalization Note** The paper's "$\delta_m\sim m^{-a}$" is read as $\delta_m=s\,m^{-a}$ for a fixed $s>0$ (p. 14: "if we scale $\delta=sm^{-a}$"); $K$ may depend on $s$. The bound is required for every $m\ge1$, not only for large $m$.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 16, Theorem 2.17 (2)

import Mathlib
import Definitions.Def_MHSpectralGap_RWM_MHKernel
import Definitions.Def_MHSpectralGap_RWM_L2Gap
import Definitions.Def_MHSpectralGap_RWM_Conductance
import Definitions.Def_MHSpectralGap_RWM_RWMKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- Theorem 2.17 (2), p. 16: for the RWM kernel `P_m` targeting `γ_m` of (2.5) with step size
`δ_m = s m^{−a}`, `a ∈ [1, ∞)`, there is `K` with `1 − β_m ≤ K m^{−a/2}` for all `m ≥ 1`. -/
theorem theorem_2_17_ii (a : ℝ) (ha : 1 ≤ a) (s : ℝ) (hs : 0 < s) :
    ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m →
      1 - l2Beta (rwmKernel m (s * (m : ℝ) ^ (-a))) (gammaM m) ≤ K * (m : ℝ) ^ (-a / 2) := by sorry

end MHSpectralGap.RWM
