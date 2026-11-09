-- Prove2me | Theorems.Thm_MatroidOptGame_lemma_2
-- name    : MatroidOptGame.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:00:20.985622+00:00
-- url     : https://prove2.me/theorems/8b06d346-0fee-4cea-9543-de4ea1b3111e
-- title:
--   Lemma 2 — $\Delta(M,w)=\infty$ iff no two disjoint bases; decidable; MAX forces $\infty$ efficiently
-- statement:
--   Let $M$ be a finite matroid with weights $w : E \to \mathbb N$, and let $\Delta(M, w)$ be the excess value of the matroid base minimization game.
--   1. $\Delta(M, w) = \infty$ if and only if $M$ does not have two disjoint bases.
--   2. Whether $M$ fails to have two disjoint bases is efficiently decidable, given an independence oracle for $M$.
--   3. If $M$ does not have two disjoint bases, MAX has an efficiently computable strategy that guarantees excess payoff $\infty$ against every legal MIN strategy.
--
--   "Efficient" means a single program of the oracle RAM, the same for every $n$, $M$ and $w$, with work at most $C(n+1)^C$ at each decision, and for the strategy at every position where MAX is to move.
--
--   **Formalization Note** In parts 2 and 3 the ground set is $\{0, \dots, n-1\}$; the decision outputs $1$ exactly when $M$ has no two disjoint bases.
--
--   Differences from the source:
--   - encoding: a matroid M = (E, I) on a finite set E → a Mathlib matroid on a finite type with M.E = Set.univ; reason: every finite matroid is of this form after relabelling its ground set by a type; no instance is lost
--   - encoding: the elements of E listed → ground set Fin n (elements labelled 0, …, n−1) in the efficiency clauses; reason: an algorithm receives the listed elements by index; every finite matroid relabels to Fin n
--   - reading: pure strategies as functions of the positive-rank minors of M → strategies as functions of the history of moves (List → Option), legal at every live position of the player's turn; reason: a minor forgets which elements were deleted and which contracted, the paper's efficient strategies are defined along the play, and the value is the same for both strategy spaces (finite perfect-information game, backward induction)
--   - reading: an efficient algorithm/strategy given an efficient independence oracle → one literal program of the published oracle RAM LSWNewArcAudit.NewArc, uniform over all n, M and w, reading n, w (and the history) from its input, reaching M only through indepOracle, with work at most C·(n+1)^C, every instruction (including arithmetic on unbounded integers and exact reals) costing one unit, and the bound independent of the weights; reason: the paper seeks tractability with respect to |E| with the matroid given by an independence oracle (pp.1, 4); work counts every instruction and query; unit-cost exact arithmetic is the house model for "efficient" (the paper's algorithms are greedy, matroid intersection and comparisons, strongly polynomial, so they run within this bound); it is a reading of "efficient" rather than a bit-complexity bound
--   - encoding: payoffs, values, δ and Δ in ℕ ∪ {∞} or ℝ ∪ {∞} → payoff and value in ℕ∞, δ, Δ and excess payoffs in EReal (2·⊤ = ⊤, ⊤ − x = ⊤); reason: Lean convention; the ∞ cases are represented, not excluded
--   - encoding: an algorithm deciding whether M does not have two disjoint bases → the program outputs 1 if M does not have two disjoint bases holds and 0 otherwise, on input gameInput n w []; reason: yes/no as 1/0; the input lists the ground set and the weights
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 2, p.5

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM
import Definitions.Def_MatroidOptGame_HasTwoDisjointBases
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_LegalMin
import Definitions.Def_MatroidOptGame_excessPayoff
import Definitions.Def_MatroidOptGame_excessValue
import Definitions.Def_MatroidOptGame_gameInput
import Definitions.Def_MatroidOptGame_ComputesWithin
import Definitions.Def_MatroidOptGame_EfficientMax

namespace MatroidOptGame

open Classical in
/-- **Lemma 2.** `Δ(M, w) = ∞` iff `M` does not have two disjoint bases. The latter condition is
efficiently decidable. If the condition holds, MAX also has an efficiently computable strategy that
guarantees excess payoff `∞`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 2, p.5.

**Formalization Note.** `M.E = Set.univ`. Strategies are functions of the history (see
`Strategy`). "Efficient" is one literal program of the oracle RAM `LSWNewArcAudit.NewArc`,
uniform over all `n`, `M` and `w`, with work at most `C·(n+1)^C` at every live position of the
player's turn; the decision outputs `1` exactly when `M` has no two disjoint bases. -/
theorem lemma_2 :
    (∀ (α : Type) [Fintype α] [DecidableEq α] (M : Matroid α), M.E = Set.univ → ∀ w : α → ℕ,
      (excessValue M w = ⊤ ↔ ¬ HasTwoDisjointBases M)) ∧
    (∃ P : LSWNewArcAudit.NewArc.OracleProgram, LSWNewArcAudit.NewArc.LiteralProgram P ∧
      ∃ C : ℕ, ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ → ∀ w : Fin n → ℕ,
        ComputesWithin P M (gameInput n w []) (C * (n + 1) ^ C)
          (if HasTwoDisjointBases M then 0 else 1)) ∧
    (∃ P : LSWNewArcAudit.NewArc.OracleProgram, LSWNewArcAudit.NewArc.LiteralProgram P ∧
      ∃ C : ℕ, ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ → ∀ w : Fin n → ℕ,
        ¬ HasTwoDisjointBases M →
        ∃ c : Strategy (Fin n), EfficientMax P C M (gameInput n w) c ∧
          ∀ s : Strategy (Fin n), LegalMin M s → excessPayoff M w c s = ⊤) := by sorry

end MatroidOptGame
