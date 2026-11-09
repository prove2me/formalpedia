-- Prove2me | Theorems.Thm_MatroidOptGame_lemma_4
-- name    : MatroidOptGame.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:39.444996+00:00
-- url     : https://prove2.me/theorems/6677144e-75f6-4b68-af7b-aedf06b53dc0
-- title:
--   Lemma 4 — deciding two disjoint bases and finding a minimum-weight disjoint pair, efficiently
-- statement:
--   Let the matroid $M$ on $E = \{0, \dots, n-1\}$ be given by its independence oracle, with weights $w : E \to \mathbb N$.
--   1. There is an efficient algorithm that decides whether $M$ has two disjoint bases.
--   2. There is an efficient algorithm that, whenever $M$ has two disjoint bases, finds disjoint bases $B_1, B_2$ of $M$ of minimum total weight:
--   $$
--   w(B_1) + w(B_2) \le w(B'_1) + w(B'_2) \quad \text{for all disjoint bases } B'_1, B'_2 \text{ of } M .
--   $$
--   "Efficient" means a single program of the oracle RAM, the same for every $n$, $M$ and $w$, whose work is bounded by $C(n+1)^C$ for a constant $C$.
--
--   **Formalization Note** The decision outputs $1$ (yes) or $0$ (no). The pair is returned as a pointer to an array of labels ($1$ for $B_1$, $2$ for $B_2$, $0$ otherwise). Both algorithms read $n$ and the weights from their input and query $M$ only through the oracle.
--
--   Differences from the source:
--   - encoding: a matroid M = (E, I) on a finite set E → a Mathlib matroid on a finite type with M.E = Set.univ; reason: every finite matroid is of this form after relabelling its ground set by a type; no instance is lost
--   - encoding: the elements of E listed → ground set Fin n (elements labelled 0, …, n−1) in the efficiency clauses; reason: an algorithm receives the listed elements by index; every finite matroid relabels to Fin n
--   - reading: an efficient algorithm/strategy given an efficient independence oracle → one literal program of the published oracle RAM LSWNewArcAudit.NewArc, uniform over all n, M and w, reading n, w (and the history) from its input, reaching M only through indepOracle, with work at most C·(n+1)^C, every instruction (including arithmetic on unbounded integers and exact reals) costing one unit, and the bound independent of the weights; reason: the paper seeks tractability with respect to |E| with the matroid given by an independence oracle (pp.1, 4); work counts every instruction and query; unit-cost exact arithmetic is the house model for "efficient" (the paper's algorithms are greedy, matroid intersection and comparisons, strongly polynomial, so they run within this bound); it is a reading of "efficient" rather than a bit-complexity bound
--   - encoding: an algorithm deciding whether M has two disjoint bases → the program outputs 1 if M has two disjoint bases holds and 0 otherwise, on input gameInput n w []; reason: yes/no as 1/0; the input lists the ground set and the weights
--   - encoding: find a pair of disjoint bases → OutputsBasePair: a pointer p with integer cells p + i labelled 1 / 2 / 0 for membership in B₁ / B₂ / neither; reason: an output convention for a pair of disjoint sets on the oracle RAM
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 4, p.5

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM
import Definitions.Def_MatroidOptGame_weight
import Definitions.Def_MatroidOptGame_HasTwoDisjointBases
import Definitions.Def_MatroidOptGame_gameInput
import Definitions.Def_MatroidOptGame_ComputesWithin
import Definitions.Def_MatroidOptGame_OutputsBasePair

namespace MatroidOptGame

open Classical in
/-- **Lemma 4.** Given an efficient independence oracle for `M`, there is an efficient algorithm to
decide if `M` has two disjoint bases. Moreover, if it does have two disjoint bases, there is an
efficient algorithm to find a pair of disjoint bases of minimum total weight.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 4, p.5.

**Formalization Note.** "Efficient" is one literal program of the oracle RAM
`LSWNewArcAudit.NewArc`, uniform over all `n`, matroids `M` on `Fin n` with `M.E = Set.univ`
(reached only through `indepOracle M`) and weights `w`, with work at most `C·(n+1)^C`. The input
is `gameInput n w []` (the ground set size and the weights). The decision outputs `1` (yes) or
`0` (no); the pair is output as a pointer to labels `1`/`2` (`OutputsBasePair`). -/
theorem lemma_4 :
    (∃ P : LSWNewArcAudit.NewArc.OracleProgram, LSWNewArcAudit.NewArc.LiteralProgram P ∧
      ∃ C : ℕ, ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ → ∀ w : Fin n → ℕ,
        ComputesWithin P M (gameInput n w []) (C * (n + 1) ^ C)
          (if HasTwoDisjointBases M then 1 else 0)) ∧
    (∃ P : LSWNewArcAudit.NewArc.OracleProgram, LSWNewArcAudit.NewArc.LiteralProgram P ∧
      ∃ C : ℕ, ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ → ∀ w : Fin n → ℕ,
        HasTwoDisjointBases M →
        ∃ B₁ B₂ : Finset (Fin n), M.IsBase (B₁ : Set (Fin n)) ∧ M.IsBase (B₂ : Set (Fin n)) ∧
          Disjoint B₁ B₂ ∧
          (∀ B₁' B₂' : Finset (Fin n), M.IsBase (B₁' : Set (Fin n)) →
            M.IsBase (B₂' : Set (Fin n)) → Disjoint B₁' B₂' →
            weight w B₁ + weight w B₂ ≤ weight w B₁' + weight w B₂') ∧
          OutputsBasePair P M (gameInput n w []) (C * (n + 1) ^ C) B₁ B₂) := by sorry

end MatroidOptGame
