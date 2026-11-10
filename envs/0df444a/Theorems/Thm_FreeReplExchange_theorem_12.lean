-- Prove2me | Theorems.Thm_FreeReplExchange_theorem_12
-- name    : FreeReplExchange.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:19:25.555202+00:00
-- url     : https://prove2.me/theorems/302f0b88-75de-4310-bdcb-cb8ea036065e
-- title:
--   Theorem 12 — M3 is IR under (19), in particular under ESC
-- statement:
--   Fix a global tie order.
--
--   1. If the utility matrices satisfy the sign conditions of §2.1 and condition (19), $(U_i)_{i,s}+(U_i)_{j,r}\ge0$ for all $i\ne j$ and $r,s$, then M3 is individually rational: for every agent $i$ and every $P\subseteq A\setminus\{i\}$,
--   $$u_i(\mathrm{M3},P\cup\{i\},\sigma^\star)\ge u_i(\mathrm{M3},P,\sigma^\star).$$
--   2. In particular, M3 is individually rational under ESC.
--
--   This is item 2 of Theorem 10.
--
--   Differences from the source:
--   - generalization: every good is initially held by at least one agent (WLOG, p.13) → any initial allocation x⁽⁰⁾; reason: no step of the proof uses the assumption; the source's instances are among those covered
--   - encoding: a total order e₁ ≺ ⋯ ≺ e_L on all potential exchanges, fixed independently of participation and history (p.32) → an injective rank rk on exchanges, smaller rank first, fixed before the participating set; reason: every total order on the finite type of exchanges arises from an injective rank, and only the order is used
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), p.35 (PDF p.37), Theorem 12

import Mathlib
import Definitions.Def_FreeReplExchange_IsEfficient
import Definitions.Def_FreeReplExchange_M3

namespace FreeReplExchange

/-- Theorem 12, Yang–Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.35 (PDF p.37). If the utility matrices satisfy (19), then M3
satisfies IR. In particular, it satisfies IR under ESC.

**Formalization Note.** The first clause assumes the sign conditions of §2.1 and (19); the second
assumes ESC (which implies both). The tie order is any injective rank, fixed independently of the
participating set. -/
theorem theorem_12 {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (rk : Exchange A m → ℕ)
    (hrk : Function.Injective rk) :
    (SignCond U → Cond19 U → IsIR x0 U (M3 x0 U rk)) ∧
      (∀ β : A → A → ℝ, IsESC U β → IsIR x0 U (M3 x0 U rk)) := by sorry

end FreeReplExchange
