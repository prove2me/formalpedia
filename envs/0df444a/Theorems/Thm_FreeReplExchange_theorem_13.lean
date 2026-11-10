-- Prove2me | Theorems.Thm_FreeReplExchange_theorem_13
-- name    : FreeReplExchange.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:19:25.382726+00:00
-- url     : https://prove2.me/theorems/6f3fa3ae-150d-4252-960e-7bb2eac444cf
-- title:
--   Theorem 13 — M3 is NIC under ESC, for any resolution of the last ties
-- statement:
--   Assume ESC: $(U_i)_{i,r}=1$ and $(U_i)_{j,r}=-\beta_{ij}$ with $\beta_{ij}=\beta_{ji}\in(0,1)$.
--
--   1. For every global tie order, M3 is Nash incentive compatible: for every $P$, every $i\in P$ and every strategy $\sigma_i$, $u_i(\mathrm{M3},P,\sigma^\star)\ge u_i(\mathrm{M3},P,(\sigma_i,\sigma^\star_{P\setminus\{i\}}))$.
--   2. The guarantee does not depend on the third optimization objective of (18): every matching protocol whose round rule selects in $G_t$ a matching lexicographically optimal for $(|\mu|,g(\mu))$, with any resolution of the remaining ties (possibly depending on the participating set and the history), terminates by the horizon and is Nash incentive compatible.
--
--   This is item 3 of Theorem 10.
--
--   Differences from the source:
--   - generalization: every good is initially held by at least one agent (WLOG, p.13) → any initial allocation x⁽⁰⁾; reason: no step of the proof uses the assumption; the source's instances are among those covered
--   - generalization: M3 with a total tie order → M3 with any rank rk, not necessarily injective; reason: the paper: the guarantee does not depend on the third objective; total orders are the injective ranks
--   - reading: "This guarantee does not depend on the third optimization objective in (18)" → NIC (and termination by the horizon) for every matching protocol whose rule is two-objective optimal in every graph, the rule possibly depending on P and the history; reason: the widest reading of "any tie-breaking rule" (p.33); it contains every history-independent rule
--   - encoding: the run until termination and its terminal allocation x⁽∞⁾ and rejected set D_∞ (p.14) → the run read at the horizon L = number of quadruples ((i,r),(j,s)), with a conjunct that the protocol has posted the empty set by then; reason: each nonterminal round removes at least one edge, so the conjunct makes the history at the horizon the terminal one
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), p.37 (PDF p.39), Theorem 13; p.33 (PDF p.35), "hold with any tie-breaking rule among matchings that optimize the first two objectives"

import Mathlib
import Definitions.Def_FreeReplExchange_IsEfficient
import Definitions.Def_FreeReplExchange_M3

namespace FreeReplExchange

/-- Theorem 13, Yang–Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.37 (PDF p.39). Under ESC, M3 satisfies NIC. This guarantee does
not depend on the third optimization objective in (18).

**Formalization Note.** The first clause is M3 with any tie order. The second clause is the
paper's second sentence: every matching protocol whose round rule (which may depend on the
participating set and the history) selects in `G_t` a matching lexicographically optimal for
`(|μ|, g(μ))`, with any resolution of the remaining ties, terminates by the horizon and is NIC. -/
theorem theorem_13 {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (β : A → A → ℝ) (hβ : IsESC U β) :
    (∀ rk : Exchange A m → ℕ, IsNIC x0 U (M3 x0 U rk)) ∧
      ∀ sel : Finset A → History A m → Finset (Exchange A m) → Finset (Exchange A m),
        IsTwoObjRule U sel →
          TerminatesByHorizon (matchProtocol x0 U sel) ∧ IsNIC x0 U (matchProtocol x0 U sel) := by sorry

end FreeReplExchange
