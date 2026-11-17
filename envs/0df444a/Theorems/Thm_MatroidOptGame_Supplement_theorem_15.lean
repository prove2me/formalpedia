-- Prove2me | Theorems.Thm_MatroidOptGame_Supplement_theorem_15
-- name    : MatroidOptGame.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:57:29.294703+00:00
-- url     : https://prove2.me/theorems/7d447221-31fa-4ae8-89b2-88170b3849d1
-- title:
--   Theorem 15 — the matroid rank maximization game has value $\lceil \tfrac12 r_{M\vee M}(E)\rceil$
-- statement:
--   Let $M$ be a matroid on a finite ground set $E$. In the **matroid rank maximization game** the two players alternately secure an element not yet secured, MAX first, until every element is secured. MAX's payoff, which MIN tries to minimize, is $r_M(E_M)$, the rank of the set $E_M$ of elements MAX secured. Let $r_{M\vee M}(E)$ be the rank of the matroid union $M\vee M$, the largest size of a union of two independent sets of $M$.
--
--   **Theorem 15.** Assume MAX goes first. Then under optimal play
--   $$
--   r_M(E_M)=\left\lceil \tfrac12\, r_{M\vee M}(E)\right\rceil .
--   $$
--   That is, MAX has a strategy guaranteeing $r_M(E_M)\ge\lceil \frac12 r_{M\vee M}(E)\rceil$ against every MIN strategy, and MIN has a strategy guaranteeing $r_M(E_M)\le\lceil \frac12 r_{M\vee M}(E)\rceil$ against every MAX strategy.
--
--   When $M$ has two disjoint bases, $r_{M\vee M}(E)=2r_M(E)$ and the value is $r_M(E)$, Lehman's maker-breaker result; the theorem gives the value of the game for every matroid, including those without two disjoint bases.
--
--   **Formalization Note** Strategies are functions of the history; legality (`FreshLegal`) asks for an unsecured element. $r_{M\vee M}(E)$ is the published `unionRank`, $r_M$ the published `rankOf`, $E_M$ the published `maxSet` of the play, and $\lceil u/2\rceil=(u+1)/2$ in $\mathbb N$.
--
--   Differences from the source:
--   - generalization: Section 3: "we focus on the case of a matroid M = (E, I) that does not have two disjoint bases" → every matroid on a finite type; reason: the proof uses neither half of the restriction, and with two disjoint bases r_{M∨M}(E) = 2r_M(E) and MAX moving first secures a base (Lehman); the restricted case is a special case
--   - encoding: "under optimal play r_M(E_M) = ⌈½ r_{M∨M}(E)⌉" → ∃ legal MAX strategy with payoff ≥ (unionRank M + 1)/2 against every legal MIN, and ∃ legal MIN strategy with payoff ≤ (unionRank M + 1)/2 against every legal MAX; reason: the value of a finite two-player perfect-information game is attained by pure strategies; ⌈u/2⌉ = (u+1)/2 in ℕ
--   - encoding: the ground set E; strategies → M.E = Set.univ on a Fintype; strategies on histories, legal at every repetition-free history of the player's parity; reason: Lean convention of the base mission; legality off the play does not change any play
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 3, Theorem 15, p.16

import Mathlib
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_maxSet
import Definitions.Def_MatroidOptGame_rankOf
import Definitions.Def_MatroidOptGame_unionRank
import Definitions.Def_MatroidOptGame_Supplement_FreshLegal
import Definitions.Def_MatroidOptGame_Supplement_rankPlay

namespace MatroidOptGame.Supplement

/-- **Theorem 15 (value of the matroid rank maximization game).** Let `M` be a matroid on a finite
ground set `E`. Players alternately secure an element not yet secured, MAX first, until every
element is secured; MAX's payoff is `r_M(E_M)`, the rank of the set `E_M` MAX secured. Under
optimal play `r_M(E_M) = ⌈½ r_{M∨M}(E)⌉`: MAX has a strategy guaranteeing `r_M(E_M) ≥ ⌈½ r_{M∨M}(E)⌉`
against every MIN strategy, and MIN has a strategy guaranteeing `r_M(E_M) ≤ ⌈½ r_{M∨M}(E)⌉` against
every MAX strategy.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 3, Theorem 15, p.16.

**Formalization Note.** `M.E = Set.univ`. `r_{M∨M}(E)` is the published `unionRank M` and
`⌈u/2⌉ = (u + 1) / 2` in `ℕ`. The statement is for every finite matroid: Section 3's "does not have
two disjoint bases" (p.16) is motivation and the proof does not use it. -/
theorem theorem_15 {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (hE : M.E = Set.univ) :
    (∃ c : Strategy α, FreshLegal 0 c ∧
        ∀ s : Strategy α, FreshLegal 1 s →
          (unionRank M + 1) / 2 ≤ rankOf M (maxSet (rankPlay c s))) ∧
      (∃ s : Strategy α, FreshLegal 1 s ∧
        ∀ c : Strategy α, FreshLegal 0 c →
          rankOf M (maxSet (rankPlay c s)) ≤ (unionRank M + 1) / 2) := by sorry

end MatroidOptGame.Supplement
