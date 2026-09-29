-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_J_abConvex_limits
-- name    : GallegoOzerADI.PositiveSetup.J_abConvex_limits
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:51:39.293848+00:00
-- url     : https://prove2.me/theorems/ff14edbe-7d87-4f98-be6d-bd74d28d1e9e
-- title:
--   Theorem 1, Part 3 — $J_t(\cdot, o_t) \in C(0,K_t)$, $J_t \to \infty$ at $+\infty$ and $J_t \to V_t(s_t(o_t), o_t)$ at $-\infty$
-- statement:
--   In the finite-horizon inventory model with advance demand information and set-up costs (Definition `Model`), with $N > L + 1$, fix a period $1 \le t \le T$ and a vector $o_t \in \mathbb{R}^{M}$. Then the optimal cost $J_t(\cdot, o_t)$ of (8) satisfies
--
--   $$
--   J_t(\cdot, o_t) \in C(0, K_t),\qquad \lim_{x \to \infty} J_t(x, o_t) = \infty,\qquad \lim_{x \to -\infty} J_t(x, o_t) = V_t(s_t(o_t), o_t),
--   $$
--
--   where $s_t(o_t) = \max\{x : H_t(x, o_t) \le 0\}$ is the reorder point.
--
--   $K_t$-convexity of $J_t$ is what propagates the $(s,S)$ structure backwards in time through the expectation in (9) (with Lemma 1, Parts 2 and 4). The limit at $-\infty$ records that a sufficiently depleted system always orders, paying the same cost.
--
--   **Formalization Note** The reorder point is asserted to exist (`IsGreatest {x | H_t(x, o_t) ≤ 0}`), and the limit at $-\infty$ is taken to its value $V_t(s_t(o_t), o_t)$.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1350, Theorem 1, Part 3 (proof p. 1356)

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model

open Filter Topology

namespace GallegoOzerADI.PositiveSetup

theorem J_abConvex_limits {L M : ℕ} [NeZero M] (P : Model L M) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ABConvex 0 (P.K t) (fun x => P.J t x o) ∧
      Tendsto (fun x => P.J t x o) atTop atTop ∧
      ∃ s : ℝ, IsGreatest {x | P.H t x o ≤ 0} s ∧
        Tendsto (fun x => P.J t x o) atBot (𝓝 (P.V t s o)) := by sorry

end GallegoOzerADI.PositiveSetup
