-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_sS_policy_optimal
-- name    : GallegoOzerADI.PositiveSetup.sS_policy_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:50:50.126414+00:00
-- url     : https://prove2.me/theorems/dd87ee7a-1d33-40e5-93af-2b1858fd6568
-- title:
--   Theorem 1, Part 2 — a state-dependent $(s_t(o_t), S_t(o_t))$ policy is optimal
-- statement:
--   In the finite-horizon inventory model with advance demand information and set-up costs (Definition `Model`), with $N > L + 1$, fix a period $1 \le t \le T$ and a vector $o_t \in \mathbb{R}^{M}$. Then the levels
--
--   $$
--   S_t(o_t) = \min\{y : V_t(y, o_t) \le V_t(x, o_t) \text{ for all } x\},\qquad
--   s_t(o_t) = \max\{x : H_t(x, o_t) \le 0\}
--   $$
--
--   exist, and the state-dependent $(s_t(o_t), S_t(o_t))$ policy attains the minimum in the functional equation (8) at every inventory position $x$:
--
--   1. if $x \le s_t(o_t)$, then $x < S_t(o_t)$ and ordering up to $S_t(o_t)$ is optimal, $J_t(x, o_t) = K_t + V_t(S_t(o_t), o_t)$;
--   2. if $x > s_t(o_t)$, then not ordering is optimal, $J_t(x, o_t) = V_t(x, o_t)$.
--
--   This is the paper's main structural result for positive set-up costs: the optimal policy is of $(s,S)$ type, with both parameters depending on the advance demand information $o_t$.
--
--   **Formalization Note** "An optimal policy" is formalized as attainment of the minimum in (8) at every state; no policy object is introduced. $S_t(o_t)$ is characterized as the least global minimizer (`IsLeast`) and $s_t(o_t)$ as the greatest element of $\{x : H_t(x, o_t) \le 0\}$ (`IsGreatest`), so both are asserted to exist.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1350, Theorem 1, Part 2 (proof p. 1356)

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model

namespace GallegoOzerADI.PositiveSetup

theorem sS_policy_optimal {L M : ℕ} [NeZero M] (P : Model L M) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ∃ S s : ℝ, IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} S ∧
      IsGreatest {x | P.H t x o ≤ 0} s ∧
      ∀ x, (x ≤ s → x < S ∧ P.J t x o = P.K t + P.V t S o) ∧
        (s < x → P.J t x o = P.V t x o) := by sorry

end GallegoOzerADI.PositiveSetup
