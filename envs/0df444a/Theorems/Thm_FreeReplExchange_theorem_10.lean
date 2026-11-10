-- Prove2me | Theorems.Thm_FreeReplExchange_theorem_10
-- name    : FreeReplExchange.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:19:30.764456+00:00
-- url     : https://prove2.me/theorems/08df009b-2d9d-42e9-930c-f502e7b670c6
-- title:
--   Theorem 10 — main guarantee of M3
-- statement:
--   Fix a finite ordered set of agents, goods $[m]$, an initial allocation $x^{(0)}$, utility matrices $U$ and a total order on all potential exchanges. For every participating set, M3 has the following properties.
--
--   1. For general utility matrices (satisfying the sign conditions $(U_i)_{i,r}\in(0,1]$, $(U_i)_{j,r}\in[-1,0)$), it satisfies MIC, stability and efficiency; every run terminates.
--   2. If (19) holds, it additionally satisfies IR.
--   3. Under ESC, it additionally satisfies NIC.
--
--   Moreover:
--
--   4. For rational utility parameters encoded in binary, each round takes time polynomial in $n$, $m$ and the encoding length of the utility parameters.
--   5. Under the accepting strategy profile, M3 uses at most one nonterminal round.
--   6. Under any strategy profile, if the initial exchange graph has at least one edge and maximum degree $\Delta$, M3 uses at most $2\Delta-1$ nonterminal rounds, and $\Delta\le(n-1)m$; if it has no edge, there is no nonterminal round. Hence the total running time is polynomial under any strategy profile.
--
--   This is the main result of the paper: a protocol without money for sharing freely replicable goods that is myopically incentive compatible, stable and efficient for general utilities, individually rational under (19), and Nash incentive compatible under ESC.
--
--   **Formalization Note** The per-round time clause is stated for Mathlib's `Turing.TM2ComputableInPolyTime` over `Bool`, on the binary code of the round state, with the lexicographic tie order $(i,j,r,s)$.
--
--   Differences from the source:
--   - generalization: every good is initially held by at least one agent (WLOG, p.13) → any initial allocation x⁽⁰⁾; reason: no step of the proof uses the assumption; the source's instances are among those covered
--   - encoding: a total order e₁ ≺ ⋯ ≺ e_L on all potential exchanges, fixed independently of participation and history (p.32) → an injective rank rk on exchanges, smaller rank first, fixed before the participating set; reason: every total order on the finite type of exchanges arises from an injective rank, and only the order is used
--   - encoding: the run until termination and its terminal allocation x⁽∞⁾ and rejected set D_∞ (p.14) → the run read at the horizon L = number of quadruples ((i,r),(j,s)), with a conjunct that the protocol has posted the empty set by then; reason: each nonterminal round removes at least one edge, so the conjunct makes the history at the horizon the terminal one
--   - reading: each round takes time polynomial in n, m and the encoding length of the utility parameters (no machine model named) → Turing.TM2ComputableInPolyTime over Bool for the binary code encRoundInput of the round state, output the incidence vector of P_t, lexicographic tie order (i, j, r, s); reason: the paper fixes rationals in binary and gives the lexicographic order as its example (p.32); a machine needs a concrete order; multi-stack Turing machines are polynomially equivalent to other standard models
--   - generalization: the state of a round of M3 (time clause) → any round input (n, m, x⁽⁰⁾, rational U with the sign conditions, P, x ≥ x⁽⁰⁾, D); reason: every round state is such an input, so the claim specializes to the rounds of M3; the sign conditions are the model's domain
--   - reading: "Since ∆ ≤ (n − 1)m, the total runtime is polynomial under any strategy profile" → per-round polynomial time, at most 2Δ − 1 nonterminal rounds, Δ ≤ (n − 1)m, and no nonterminal round when the initial graph has no edge; reason: the paper derives the sentence from exactly these facts (p.39); the round's state is computed from the history in the same time
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), pp.33–34 (PDF pp.35–36), Theorem 10; p.39 (PDF p.41), last paragraph of §5.4.2

import Mathlib
import Definitions.Def_FreeReplExchange_IsEfficient
import Definitions.Def_FreeReplExchange_M3
import Definitions.Def_FreeReplExchange_m3RoundQ

namespace FreeReplExchange

/-- Theorem 10 (Main guarantee), Yang–Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with
Negative Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.33–34 (PDF pp.35–36). For every participating set, M3
has the following properties. 1. For general utility matrices, it satisfies MIC, stability, and
efficiency. 2. If (19) holds, it additionally satisfies IR. 3. Under ESC, it additionally satisfies
NIC. For rational utility parameters encoded in binary, each round takes time polynomial in `n`,
`m`, and the encoding length of the utility parameters. Under the accepting strategy profile, M3 uses
at most one nonterminal round. Under any strategy profile, if the initial exchange graph has at least
one edge and maximum degree `∆`, M3 uses at most `2∆ − 1` nonterminal rounds. Since
`∆ ≤ (n − 1)m`, the total runtime is polynomial under any strategy profile.

**Formalization Note.** Agents are a finite linearly ordered type, goods `Fin m`; the global tie
order is any injective rank `rk` on exchanges. Runs are read at a horizon (the number of
quadruples); the first clause includes that every run has stopped by then, so `x^(∞)` and `D_∞` are
the terminal ones. "General utility matrices" are those satisfying the sign conditions of §2.1;
ESC implies them. The time clause uses Mathlib's `Turing.TM2ComputableInPolyTime` over `Bool`, the
binary code `encRoundInput` and the lexicographic tie order `(i, j, r, s)`. "The total runtime is
polynomial" is rendered by its three ingredients (p.39): per-round polynomial time, at most
`2∆ − 1` nonterminal rounds, and `∆ ≤ (n − 1)m`; with no edge there is no nonterminal round. -/
theorem theorem_10 {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (rk : Exchange A m → ℕ)
    (hrk : Function.Injective rk) :
    (SignCond U → TerminatesByHorizon (M3 x0 U rk) ∧ IsMIC x0 U (M3 x0 U rk) ∧
        IsStable x0 U (M3 x0 U rk) ∧ IsEfficient x0 U (M3 x0 U rk)) ∧
    (SignCond U → Cond19 U → IsIR x0 U (M3 x0 U rk)) ∧
    (∀ β : A → A → ℝ, IsESC U β → IsNIC x0 U (M3 x0 U rk)) ∧
    (SignCond U → ∀ P : Finset A, nonterminalRounds (M3 x0 U rk) P acceptAll ≤ 1) ∧
    (SignCond U → ∀ (P : Finset A) (σ : A → Strategy A m), (edges x0 U P x0).Nonempty →
        nonterminalRounds (M3 x0 U rk) P σ ≤ 2 * maxDeg (edges x0 U P x0) - 1 ∧
          maxDeg (edges x0 U P x0) ≤ (Fintype.card A - 1) * m) ∧
    (SignCond U → ∀ (P : Finset A) (σ : A → Strategy A m), edges x0 U P x0 = ∅ →
        nonterminalRounds (M3 x0 U rk) P σ = 0) ∧
    Nonempty (Turing.TM2ComputableInPolyTime encRoundInput (fun l : List Bool => l) m3RoundQ) := by sorry

end FreeReplExchange
