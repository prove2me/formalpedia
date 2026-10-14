-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_theorem_1_2_i
-- name    : GPhNGIDiffusion.EMError.theorem_1_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:46.745977+00:00
-- url     : https://prove2.me/theorems/f41981b7-7804-4ebb-971f-a0a1170cc0a8
-- title:
--   Theorem 1.2(i): the Euler–Maruyama chain has a unique invariant $\tilde\mu_\eta$ and $d_W(\mu,\tilde\mu_\eta)\le C_\varsigma\eta^{(1-\varsigma)/2}$
-- statement:
--   Let the limiting diffusion of the $G/Ph/n+GI$ queue in the Halfin–Whitt regime be
--   $$
--   dX_t=g(X_t)\,dt+\sigma\,dB_t,\qquad g(x)=-\beta p-Rx+(R-\alpha I)p\,(e'x)^+,
--   $$
--   with transition function $(P_t)_{t\ge0}$ and invariant probability measure $\mu$, and let
--   $$
--   \tilde X^\eta_{k+1}=\tilde X^\eta_k+g(\tilde X^\eta_k)\eta+\sqrt\eta\,\sigma\xi_{k+1},\qquad k\in\mathbb N_0,
--   $$
--   be its Euler–Maruyama scheme with step $\eta$ and independent standard Gaussian $\xi_k$. There is $\eta_0>0$ such that for every $\varsigma\in(0,1)$ there is a constant $C_\varsigma>0$, depending on $\varsigma$ but not on $\eta$, such that for every $\eta\in(0,\eta_0]$ the chain $(\tilde X^\eta_k)_{k\in\mathbb N_0}$ admits a unique invariant probability measure $\tilde\mu_\eta$, and
--   $$
--   d_W(\mu,\tilde\mu_\eta)\le C_\varsigma\,\eta^{\frac{1-\varsigma}{2}},
--   $$
--   where $d_W$ is the Wasserstein-1 distance (1.5).
--
--   The invariant measure of this multidimensional diffusion with piecewise-linear drift has no explicit form; the theorem makes the Euler–Maruyama chain a computable approximation of it, with a non-asymptotic error bound in the Wasserstein-1 distance.
--
--   **Formalization Note** The theorem's first sentence also asserts that the chain is exponentially ergodic; that quantitative statement is Proposition 2.1, a milestone of this mission, and is not repeated here. "For any small enough $\varsigma\in(0,1)$" is rendered as every $\varsigma\in(0,1)$: for $\eta\le1$ the bound weakens as $\varsigma$ grows, so the readings agree once $\eta_0\le1$. The threshold $\eta_0$ is implicit in the paper ("small $\eta$", from Proposition 2.1 and Lemma A.4) and is chosen before $\varsigma$; $C_\varsigma$ is chosen before $\eta$. $\mu$ enters as a hypothesis: the diffusion has exactly one invariant probability measure (Dieker and Gao, Theorem 3). $d_W$ is $+\infty$ unless both measures have finite first moments, so the bound also asserts that $\tilde\mu_\eta$ and $\mu$ have them.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 3, Theorem 1.2 (first sentence and (i)); proof pp. 9-11

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Model
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_EulerMaruyama
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace GPhNGIDiffusion.EMError

/-- Theorem 1.2 (first sentence and (i)), p. 3: let `µ` be the invariant probability measure of the
limiting diffusion (1.1). There is `η₀ > 0` such that for every `ς ∈ (0, 1)` there is `C_ς > 0`,
depending on `ς` but not on `η`, such that for every step `η ∈ (0, η₀]` the Euler–Maruyama chain
(1.2) has a unique invariant probability measure `µ̃_η`, and `d_W(µ, µ̃_η) ≤ C_ς η^{(1−ς)/2}`. -/
theorem theorem_1_2_i {d : ℕ} (M : Model d)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hP : IsTransitionFunction M.drift M.σ P)
    (μ : Measure (EthierKurtz.SDEState d)) (hμ : IsInvariantMeasure P μ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ ς : ℝ, 0 < ς → ς < 1 → ∃ Cς : ℝ, 0 < Cς ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        (∃! μt : Measure (EthierKurtz.SDEState d), IsEMInvariant M.drift M.σ η μt) ∧
        ∀ μt : Measure (EthierKurtz.SDEState d), IsEMInvariant M.drift M.σ η μt →
          dW μ μt ≤ ENNReal.ofReal (Cς * η ^ ((1 - ς) / 2)) := by sorry

end GPhNGIDiffusion.EMError
