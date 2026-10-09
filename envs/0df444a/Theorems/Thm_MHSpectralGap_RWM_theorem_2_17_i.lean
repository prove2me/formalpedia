-- Prove2me | Theorems.Thm_MHSpectralGap_RWM_theorem_2_17_i
-- name    : MHSpectralGap.RWM.theorem_2_17_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:17:32.788822+00:00
-- url     : https://prove2.me/theorems/4dfc222a-e36b-423d-af6e-8a08a00bd0ba
-- title:
--   Theorem 2.17 (1), p. 15 — for δ_m = s m^{−a}, a ∈ [0, 1), the L²-spectral gap of RWM on γ_m satisfies 1 − β_m ≤ K(p, a) m^{−p} for every p
-- statement:
--   For $m\ge1$ let $\gamma_m$ be the Gaussian measure (2.5) on $\mathbb R^m$, the law of $\sum_{i=1}^m\frac1i\xi_ie_i$ with $\xi_i$ i.i.d. standard normal, and let $P_m$ be the random walk Metropolis kernel targeting $\gamma_m$ with step size $\delta_m=s\,m^{-a}$ (proposal $y=x+\sqrt{2\delta_m}\,\xi$, $\xi\sim\gamma_m$, accepted with probability $1\wedge\exp(\sum_i\frac{i^2}2(x_i^2-y_i^2))$), where $s>0$ is fixed. Let $\beta_m=\|P_m\|_{L^2_0\to L^2_0}$ (Definition 2.7 with $\mu=\gamma_m$), so that $1-\beta_m$ is the $L^2_{\gamma_m}$-spectral gap of $P_m$. If $a\in[0,1)$, then for every $p$ there is a constant $K$, depending on $p$, $a$ and $s$ but not on $m$, such that for all $m\ge1$
--
--   $$
--   1-\beta_m\;\le\;K\,m^{-p}.
--   $$
--
--   The spectral gap of random walk Metropolis therefore vanishes faster than any negative power of the dimension when the step size decays more slowly than $1/m$, in contrast with the preconditioned Crank–Nicolson algorithm, whose spectral gap for the same targets is bounded below uniformly in $m$ (Theorem 2.14 with $\Phi=0$).
--
--   **Formalization Note** The paper's "$\delta_m\sim m^{-a}$" is read as $\delta_m=s\,m^{-a}$ for a fixed $s>0$ (p. 14: "if we scale $\delta=sm^{-a}$"); $K$ may depend on $s$, which the paper's $K(p,a)$ leaves implicit. "Any $p$" is read as every real $p$. The bound is required for every $m\ge1$ (the constant absorbs small $m$), not only for large $m$. $\beta_m$ is the real supremum of Definition 2.7; for $m\ge1$ that supremum is over a nonempty set bounded by $1$.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 15, Theorem 2.17 (1)

import Mathlib
import Definitions.Def_MHSpectralGap_RWM_MHKernel
import Definitions.Def_MHSpectralGap_RWM_L2Gap
import Definitions.Def_MHSpectralGap_RWM_Conductance
import Definitions.Def_MHSpectralGap_RWM_RWMKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- Theorem 2.17 (1), p. 15: for the RWM kernel `P_m` targeting `γ_m` of (2.5) with step size
`δ_m = s m^{−a}`, `a ∈ [0, 1)`, and any `p`, there is `K` with `1 − β_m ≤ K m^{−p}` for all
`m ≥ 1`. -/
theorem theorem_2_17_i (a : ℝ) (ha : a ∈ Set.Ico (0 : ℝ) 1) (s : ℝ) (hs : 0 < s) (p : ℝ) :
    ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m →
      1 - l2Beta (rwmKernel m (s * (m : ℝ) ^ (-a))) (gammaM m) ≤ K * (m : ℝ) ^ (-p) := by sorry

end MHSpectralGap.RWM
