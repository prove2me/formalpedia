-- Prove2me | Theorems.Thm_NicaiseDelayWave_BoundaryInstab_theorem1_2_destabilizing_delays
-- name    : NicaiseDelayWave.BoundaryInstab.theorem1_2_destabilizing_delays
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T21:16:41.050402+00:00
-- url     : https://prove2.me/theorems/a5ee0c39-4c73-405e-9fc5-17b7f9890345
-- title:
--   Theorem 1.2 — if μ2 ≥ μ1, there are delays τ_k and solutions of the delayed boundary problem with constant positive standard energy
-- statement:
--   Let $n \ge 1$ and let $(\Omega, \Gamma_D, \Gamma_N)$ be a mixed domain: $\Omega \subset \mathbb R^n$ bounded, open, with $C^2$ boundary $\Gamma = \Gamma_D \cup \Gamma_N$, $\overline{\Gamma_D} \cap \overline{\Gamma_N} = \emptyset$, $\Gamma_D \ne \emptyset$. Let $\mu_1, \mu_2 > 0$ and suppose that (1.8) does not hold, i.e.
--   $$\mu_2 \ge \mu_1 .$$
--   Then there exist a strictly increasing sequence of delays $0 < \tau_0 < \tau_1 < \cdots$ and, for each $k$, a classical solution $u_k$ of
--   $$\begin{cases} u_{tt} - \Delta u = 0 & \text{in } \Omega \times (0,+\infty),\\ u = 0 & \text{on } \Gamma_D \times (0,+\infty),\\ \dfrac{\partial u}{\partial\nu}(x,t) = -\mu_1 u_t(x,t) - \mu_2 u_t(x,t-\tau_k) & \text{on } \Gamma_N \times (0,+\infty), \end{cases}$$
--   whose standard energy
--   $$\mathcal E_k(t) = \frac12\int_\Omega \big(|u_{k,t}(x,t)|^2 + |\nabla u_k(x,t)|^2\big)\,dx$$
--   is constant and positive for $t \ge 0$: there is $c_k > 0$ with $\mathcal E_k(t) = c_k$ for all $t \ge 0$.
--
--   In particular, when $\mu_2 \ge \mu_1$ the delayed boundary feedback is not asymptotically stable for these delays, in contrast with the exponential decay of Theorem 1.1 when $\mu_2 < \mu_1$.
--
--   **Formalization Note**
--   1. Solutions are complex-valued, as are the page's $u = e^{ibt}\varphi$ ($|u_t|^2$, $|\nabla u|^2$ are squared moduli); for real solutions the constancy of the energy fails in case (b).
--   2. A solution is $C^2$ in $\Omega \times \mathbb R$ and $C^1$ on $\overline\Omega\times\mathbb R$, with the normal derivative taken within $\overline\Omega$; its values at $t \le 0$ are the initial data (1.4)–(1.5).
--   3. "Constant" is required together with $c_k > 0$, which is the page's intent (it computes $2b^2 > 0$ in case (a)): without positivity the zero solution would satisfy the statement.
--   4. "A sequence of delays" is rendered as a strictly increasing sequence of positive delays.
--   5. The geometric hypotheses (1.6)–(1.7) and the parameter $\xi$ of (1.10) play no role in §5.1 and are omitted, which makes the statement stronger.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1563, Theorem 1.2 (proof in §5.1, pp. 1579–1582)

import Mathlib
import Definitions.Def_NicaiseDelayWave_Shared_MixedDomain
import Definitions.Def_NicaiseDelayWave_BoundaryInstab_DelayProblem

open MeasureTheory

namespace NicaiseDelayWave.BoundaryInstab

/-- Theorem 1.2: if (1.8) fails, i.e. `μ₂ ≥ μ₁`, there are a strictly increasing sequence of
positive delays `τ_k` and, for each `k`, a classical (complex-valued) solution of (1.1)–(1.3)
with delay `τ_k` whose standard energy is constant and positive for `t ≥ 0`. -/
theorem theorem1_2_destabilizing_delays {n : ℕ} (hn : 1 ≤ n) (D : NicaiseDelayWave.Shared.MixedDomain n)
    (μ1 μ2 : ℝ) (hμ1 : 0 < μ1) (hμ2 : 0 < μ2) (h18 : μ1 ≤ μ2) :
    ∃ τs : ℕ → ℝ, StrictMono τs ∧ (∀ k, 0 < τs k) ∧
      ∀ k, ∃ u : EuclideanSpace ℝ (Fin n) → ℝ → ℂ,
        IsClassicalSolution D μ1 μ2 (τs k) u ∧
          ∃ c : ℝ, 0 < c ∧ ∀ t ≥ 0, stdEnergy D u t = c := by sorry

end NicaiseDelayWave.BoundaryInstab
