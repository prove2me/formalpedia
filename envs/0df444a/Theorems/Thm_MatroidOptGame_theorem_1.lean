-- Prove2me | Theorems.Thm_MatroidOptGame_theorem_1
-- name    : MatroidOptGame.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:01:21.849168+00:00
-- url     : https://prove2.me/theorems/a933a044-3f11-49df-9d1b-4c9d9f4fad36
-- title:
--   Theorem 1 — $\delta \le \Delta \le 2\delta$ in the matroid base minimization game, with efficient MAX and MIN strategies
-- statement:
--   Consider the matroid base minimization game on a finite matroid $M = (E, \mathcal I)$ with weights $w : E \to \mathbb N$: MAX moves first and deletes an element, MIN then contracts a non-loop element, and so on; the game ends when MAX's deletions include a cut (payoff $\infty$) or MIN's contractions form a base $S$ (payoff $w(S)$). Let $\Delta(M, w) = V(M, w) - w(B_{\min}(M, w))$ be its excess value and $\delta(M, w)$ the quantity defined from the matroid union $M \vee M$. Then:
--   1. for every finite matroid $M$ and every $w : E \to \mathbb N$,
--   $$
--   \delta(M, w) \;\le\; \Delta(M, w) \;\le\; 2\,\delta(M, w);
--   $$
--   2. given an independence oracle, MAX has an efficient strategy that achieves excess payoff at least $\delta(M, w)$ against every legal MIN strategy;
--   3. given an independence oracle, MIN has an efficient strategy that keeps MAX's excess payoff at most $2\,\delta(M, w)$ against every legal MAX strategy.
--
--   Part 1 includes the cases $\delta = \infty$ (no two disjoint bases) and $\delta = 0$. In parts 2 and 3, "efficient" means one program of the oracle RAM for each player, the same for every $n = |E|$, matroid and weight function, which computes the player's move at every position where that player is to move within work $C(n+1)^C$, reading $n$, $w$ and the history and querying $M$ only through its independence oracle.
--
--   **Formalization Note** In parts 2 and 3 the ground set is $\{0, \dots, n-1\}$. Values, $\delta$ and excess payoffs are extended reals, with $2\cdot\infty = \infty$.
--
--   Differences from the source:
--   - encoding: a matroid M = (E, I) on a finite set E → a Mathlib matroid on a finite type with M.E = Set.univ; reason: every finite matroid is of this form after relabelling its ground set by a type; no instance is lost
--   - encoding: the elements of E listed → ground set Fin n (elements labelled 0, …, n−1) in the efficiency clauses; reason: an algorithm receives the listed elements by index; every finite matroid relabels to Fin n
--   - reading: pure strategies as functions of the positive-rank minors of M → strategies as functions of the history of moves (List → Option), legal at every live position of the player's turn; reason: a minor forgets which elements were deleted and which contracted, the paper's efficient strategies are defined along the play, and the value is the same for both strategy spaces (finite perfect-information game, backward induction)
--   - reading: an efficient algorithm/strategy given an efficient independence oracle → one literal program of the published oracle RAM LSWNewArcAudit.NewArc, uniform over all n, M and w, reading n, w (and the history) from its input, reaching M only through indepOracle, with work at most C·(n+1)^C, every instruction (including arithmetic on unbounded integers and exact reals) costing one unit, and the bound independent of the weights; reason: the paper seeks tractability with respect to |E| with the matroid given by an independence oracle (pp.1, 4); work counts every instruction and query; unit-cost exact arithmetic is the house model for "efficient" (the paper's algorithms are greedy, matroid intersection and comparisons, strongly polynomial, so they run within this bound); it is a reading of "efficient" rather than a bit-complexity bound
--   - encoding: payoffs, values, δ and Δ in ℕ ∪ {∞} or ℝ ∪ {∞} → payoff and value in ℕ∞, δ, Δ and excess payoffs in EReal (2·⊤ = ⊤, ⊤ − x = ⊤); reason: Lean convention; the ∞ cases are represented, not excluded
--   - encoding: the matroid union M ∨ M and its bases → the set system {I ∪ J : I, J independent}; r_{M∨M}(E) its maximum size, B_min(M ∨ M, w) a minimum-weight set of that size; reason: M ∨ M is a matroid (p.20), so its bases are exactly its maximum-size independent sets; Mathlib has no matroid union
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.1, Theorem 1, p.4

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM
import Definitions.Def_MatroidOptGame_delta
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_LegalMax
import Definitions.Def_MatroidOptGame_LegalMin
import Definitions.Def_MatroidOptGame_excessPayoff
import Definitions.Def_MatroidOptGame_excessValue
import Definitions.Def_MatroidOptGame_gameInput
import Definitions.Def_MatroidOptGame_EfficientMax
import Definitions.Def_MatroidOptGame_EfficientMin

namespace MatroidOptGame

/-- **Theorem 1.** For every matroid `M = (E, I)` and every weight function `w : E → ℕ`,
`δ(M, w) ≤ Δ(M, w) ≤ 2δ(M, w)`. Moreover, given an efficient independence oracle, there is an
efficient strategy for MAX that achieves excess payoff at least `δ(M, w)`, and there is an
efficient strategy for MIN that restricts the excess payoff to be at most `2δ(M, w)`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.1, Theorem 1, p.4.

**Formalization Note.** `M.E = Set.univ` (for the efficiency clauses the ground set is `Fin n`,
the labels of the listed elements). `δ`, `Δ` and excess payoffs are in `EReal` (`2·⊤ = ⊤`), so the
cases `δ = ∞` and `δ = 0` are included. Strategies are functions of the history; MAX moves first.
"Efficient" is one literal program of the oracle RAM `LSWNewArcAudit.NewArc` for each player,
uniform over all `n`, `M` and `w`, reading `n`, `w` and the history from `gameInput n w h`,
reaching `M` only through its independence oracle, with work at most `C·(n+1)^C` at every live
position of that player's turn. The guarantees hold against every legal opposing strategy. -/
theorem theorem_1 :
    (∀ (α : Type) [Fintype α] [DecidableEq α] (M : Matroid α), M.E = Set.univ → ∀ w : α → ℕ,
      delta M w ≤ excessValue M w ∧ excessValue M w ≤ 2 * delta M w) ∧
    (∃ P : LSWNewArcAudit.NewArc.OracleProgram, LSWNewArcAudit.NewArc.LiteralProgram P ∧
      ∃ C : ℕ, ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ → ∀ w : Fin n → ℕ,
        ∃ c : Strategy (Fin n), EfficientMax P C M (gameInput n w) c ∧
          ∀ s : Strategy (Fin n), LegalMin M s → delta M w ≤ excessPayoff M w c s) ∧
    (∃ P : LSWNewArcAudit.NewArc.OracleProgram, LSWNewArcAudit.NewArc.LiteralProgram P ∧
      ∃ C : ℕ, ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ → ∀ w : Fin n → ℕ,
        ∃ s : Strategy (Fin n), EfficientMin P C M (gameInput n w) s ∧
          ∀ c : Strategy (Fin n), LegalMax M c → excessPayoff M w c s ≤ 2 * delta M w) := by sorry

end MatroidOptGame
