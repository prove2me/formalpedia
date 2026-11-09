-- Prove2me | Theorems.Thm_MatroidOptGame_lemma_5
-- name    : MatroidOptGame.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:58:50.169075+00:00
-- url     : https://prove2.me/theorems/36a3f03a-83ac-478c-ae13-2aadd9fb35a5
-- title:
--   Lemma 5 — two disjoint minimum-weight bases: decidable, and MIN secures excess $0$ efficiently
-- statement:
--   Let the matroid $M$ on $E = \{0, \dots, n-1\}$ be given by its independence oracle, with weights $w : E \to \mathbb N$.
--   1. It can be decided efficiently whether $M$ has two disjoint minimum-weight bases.
--   2. If it has, MIN has an efficient strategy that guarantees MAX excess payoff $0$: against every legal MAX strategy $c$,
--   $$
--   p(c, s) - w(B_{\min}(M, w)) = 0 .
--   $$
--   "Efficient" means a single program of the oracle RAM, the same for every $n$, $M$ and $w$, with work at most $C(n+1)^C$ for the decision and at every position where MIN is to move.
--
--   **Formalization Note** The decision outputs $1$ (yes) or $0$ (no). The strategy reads $n$, $w$ and the history from its input.
--
--   Differences from the source:
--   - encoding: a matroid M = (E, I) on a finite set E → a Mathlib matroid on a finite type with M.E = Set.univ; reason: every finite matroid is of this form after relabelling its ground set by a type; no instance is lost
--   - encoding: the elements of E listed → ground set Fin n (elements labelled 0, …, n−1) in the efficiency clauses; reason: an algorithm receives the listed elements by index; every finite matroid relabels to Fin n
--   - reading: pure strategies as functions of the positive-rank minors of M → strategies as functions of the history of moves (List → Option), legal at every live position of the player's turn; reason: a minor forgets which elements were deleted and which contracted, the paper's efficient strategies are defined along the play, and the value is the same for both strategy spaces (finite perfect-information game, backward induction)
--   - reading: an efficient algorithm/strategy given an efficient independence oracle → one literal program of the published oracle RAM LSWNewArcAudit.NewArc, uniform over all n, M and w, reading n, w (and the history) from its input, reaching M only through indepOracle, with work at most C·(n+1)^C, every instruction (including arithmetic on unbounded integers and exact reals) costing one unit, and the bound independent of the weights; reason: the paper seeks tractability with respect to |E| with the matroid given by an independence oracle (pp.1, 4); work counts every instruction and query; unit-cost exact arithmetic is the house model for "efficient" (the paper's algorithms are greedy, matroid intersection and comparisons, strongly polynomial, so they run within this bound); it is a reading of "efficient" rather than a bit-complexity bound
--   - encoding: payoffs, values, δ and Δ in ℕ ∪ {∞} or ℝ ∪ {∞} → payoff and value in ℕ∞, δ, Δ and excess payoffs in EReal (2·⊤ = ⊤, ⊤ − x = ⊤); reason: Lean convention; the ∞ cases are represented, not excluded
--   - encoding: an algorithm deciding whether M has two disjoint minimum-weight bases → the program outputs 1 if M has two disjoint minimum-weight bases holds and 0 otherwise, on input gameInput n w []; reason: yes/no as 1/0; the input lists the ground set and the weights
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 5, p.6

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM
import Definitions.Def_MatroidOptGame_HasTwoDisjointMinBases
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_LegalMax
import Definitions.Def_MatroidOptGame_excessPayoff
import Definitions.Def_MatroidOptGame_gameInput
import Definitions.Def_MatroidOptGame_ComputesWithin
import Definitions.Def_MatroidOptGame_EfficientMin

namespace MatroidOptGame

open Classical in
/-- **Lemma 5.** It can be decided efficiently if `M` has two disjoint minimum-weight bases. If this
is the case, then MIN has an efficient strategy that guarantees excess payoff `0`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 5, p.6.

**Formalization Note.** `M.E = Set.univ`; strategies on histories; "efficient" is one literal
program of the oracle RAM `LSWNewArcAudit.NewArc`, uniform over all `n`, `M`, `w`, with work at
most `C·(n+1)^C` at every live position of MIN's turn. The decision outputs `1` (yes) or `0`. -/
theorem lemma_5 :
    (∃ P : LSWNewArcAudit.NewArc.OracleProgram, LSWNewArcAudit.NewArc.LiteralProgram P ∧
      ∃ C : ℕ, ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ → ∀ w : Fin n → ℕ,
        ComputesWithin P M (gameInput n w []) (C * (n + 1) ^ C)
          (if HasTwoDisjointMinBases M w then 1 else 0)) ∧
    (∃ P : LSWNewArcAudit.NewArc.OracleProgram, LSWNewArcAudit.NewArc.LiteralProgram P ∧
      ∃ C : ℕ, ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ → ∀ w : Fin n → ℕ,
        HasTwoDisjointMinBases M w →
        ∃ s : Strategy (Fin n), EfficientMin P C M (gameInput n w) s ∧
          ∀ c : Strategy (Fin n), LegalMax M c → excessPayoff M w c s = 0) := by sorry

end MatroidOptGame
