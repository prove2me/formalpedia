-- Prove2me | Theorems.Thm_MatroidOptGame_lemma_6
-- name    : MatroidOptGame.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:58:03.215478+00:00
-- url     : https://prove2.me/theorems/649dd140-b0e8-4404-8d27-3db791bccd92
-- title:
--   Lemma 6 — given two disjoint bases, MIN holds the excess to $w(B_1)+w(B_2)-2w(B_{\min})$
-- statement:
--   Let the matroid $M$ on $E = \{0, \dots, n-1\}$ be given by its independence oracle, with weights $w : E \to \mathbb N$. Given two disjoint bases $B_1, B_2$ of $M$, MIN has an efficient strategy $s$ such that, against every legal MAX strategy $c$,
--   $$
--   p(c, s) - w(B_{\min}(M, w)) \;\le\; w(B_1) + w(B_2) - 2\,w(B_{\min}(M, w)).
--   $$
--   "Efficient" means a single program of the oracle RAM, the same for every $n$, $M$, $w$, $B_1$, $B_2$, that receives $B_1$ and $B_2$ as part of its input and computes MIN's move at every position where MIN is to move within work $C(n+1)^C$.
--
--   **Formalization Note** The bound is on the excess payoff in the extended reals; in particular MIN always completes a base.
--
--   Differences from the source:
--   - encoding: a matroid M = (E, I) on a finite set E → a Mathlib matroid on a finite type with M.E = Set.univ; reason: every finite matroid is of this form after relabelling its ground set by a type; no instance is lost
--   - encoding: the elements of E listed → ground set Fin n (elements labelled 0, …, n−1) in the efficiency clauses; reason: an algorithm receives the listed elements by index; every finite matroid relabels to Fin n
--   - reading: pure strategies as functions of the positive-rank minors of M → strategies as functions of the history of moves (List → Option), legal at every live position of the player's turn; reason: a minor forgets which elements were deleted and which contracted, the paper's efficient strategies are defined along the play, and the value is the same for both strategy spaces (finite perfect-information game, backward induction)
--   - reading: an efficient algorithm/strategy given an efficient independence oracle → one literal program of the published oracle RAM LSWNewArcAudit.NewArc, uniform over all n, M and w, reading n, w (and the history) from its input, reaching M only through indepOracle, with work at most C·(n+1)^C, every instruction (including arithmetic on unbounded integers and exact reals) costing one unit, and the bound independent of the weights; reason: the paper seeks tractability with respect to |E| with the matroid given by an independence oracle (pp.1, 4); work counts every instruction and query; unit-cost exact arithmetic is the house model for "efficient" (the paper's algorithms are greedy, matroid intersection and comparisons, strongly polynomial, so they run within this bound); it is a reading of "efficient" rather than a bit-complexity bound
--   - encoding: payoffs, values, δ and Δ in ℕ ∪ {∞} or ℝ ∪ {∞} → payoff and value in ℕ∞, δ, Δ and excess payoffs in EReal (2·⊤ = ⊤, ⊤ − x = ⊤); reason: Lean convention; the ∞ cases are represented, not excluded
--   - encoding: given two disjoint bases B1, B2 → B₁, B₂ written into the program's input (pairInput n w B₁ B₂ h); reason: "given" means the bases are input to the strategy's algorithm
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 6, p.6

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM
import Definitions.Def_MatroidOptGame_weight
import Definitions.Def_MatroidOptGame_minBaseWeight
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_LegalMax
import Definitions.Def_MatroidOptGame_excessPayoff
import Definitions.Def_MatroidOptGame_pairInput
import Definitions.Def_MatroidOptGame_EfficientMin

namespace MatroidOptGame

/-- **Lemma 6.** Given two disjoint bases `B₁, B₂` of `M`, MIN has an efficient strategy to secure
a bound of at most `w(B₁) + w(B₂) − 2·w(B_min(M, w))` on MAX's excess payoff.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 6, p.6.

**Formalization Note.** `M.E = Set.univ`; strategies on histories; "efficient" is one literal
program of the oracle RAM `LSWNewArcAudit.NewArc`, uniform over all `n`, `M`, `w`, `B₁`, `B₂`,
with work at most `C·(n+1)^C` at every live position of MIN's turn. The two bases are given:
they are part of the program's input (`pairInput n w B₁ B₂ h`). -/
theorem lemma_6 :
    ∃ P : LSWNewArcAudit.NewArc.OracleProgram, LSWNewArcAudit.NewArc.LiteralProgram P ∧
      ∃ C : ℕ, ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
        ∀ (w : Fin n → ℕ) (B₁ B₂ : Finset (Fin n)),
          M.IsBase (B₁ : Set (Fin n)) → M.IsBase (B₂ : Set (Fin n)) → Disjoint B₁ B₂ →
          ∃ s : Strategy (Fin n), EfficientMin P C M (pairInput n w B₁ B₂) s ∧
            ∀ c : Strategy (Fin n), LegalMax M c →
              excessPayoff M w c s ≤
                ((((weight w B₁ + weight w B₂ : ℕ) : ℝ) - 2 * (minBaseWeight M w : ℝ) : ℝ) : EReal) := by sorry

end MatroidOptGame
