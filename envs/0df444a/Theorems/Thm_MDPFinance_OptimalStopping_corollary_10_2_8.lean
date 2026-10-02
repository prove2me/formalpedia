-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_corollary_10_2_8
-- name    : MDPFinance.OptimalStopping.corollary_10_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:45:14.964931+00:00
-- url     : https://prove2.me/theorems/be91e527-28e2-45c5-a0c2-cbb46b9b748f
-- title:
--   Corollary 10.2.8 — the monotone case gives a threshold rule
-- statement:
--   **Corollary 10.2.8** (pp. 316-317). Suppose $E$ is a completely ordered space. Assume that
--   we are in the **monotone case**, i.e. the assumptions of Theorem 10.2.7 are satisfied and that
--
--   (i) $x \mapsto g(x)$ is increasing,
--   (ii) $x \mapsto c(x)$ is decreasing,
--   (iii) $x \mapsto \int g(x')Q^X(dx'|x)$ is decreasing.
--
--   Let $\tau^*$ be defined as in Theorem 10.2.7. If $\mathbb{P}_x(\tau^* < \infty) = 1$ for all
--   $x \in E$, then the optimal stopping time is of **threshold type**.
--
--   The proof is one line once 10.2.7 is in hand: the three monotonicity assumptions make
--   $x \mapsto g(x) - c(x) - \beta\int g(x')Q^X(dx'|x)$ increasing, so $S_0$ is an up-set.
--
--   "Of threshold type" is spelled out here as Remark 10.1.6 (p. 308) spells it out: $S_0$ is upward
--   closed, and therefore either empty, all of $E$, or cut out by a threshold $x^*$ in the sense that
--   every state strictly above $x^*$ stops and every state that stops is at least $x^*$. The two-sided
--   form is what a general completely ordered space allows — the book's
--   $x^* := \inf\{x \in E \mid d(x) \ge 0\}$ need not itself lie in $S_0$.
--
--   Note that (ii) and (iii) are *decreasing* while (i) is *increasing*. Making all three increasing
--   would not give the conclusion: it is the difference $g - c - \beta\int g\,dQ^X$ that must be
--   monotone, and the signs in front of $c$ and $\int g\,dQ^X$ are negative.
--
--   **Moderation note.** The draft's threshold trichotomy is false in a general linear order (an upper set of `ℚ` cut at an irrational has no threshold in `E`); the book's `x^* := inf{…}` presumes infima, so `E` is now a conditionally complete linear order, where the trichotomy holds. Monotonicity (iii) is for the `[-∞,∞]`-valued integral.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, pp. 316-317 (PDF 323-324), Corollary 10.2.8

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology

namespace MDPFinance.OptimalStopping

/-- **Corollary 10.2.8** (pp. 315-316). `E` completely ordered (a conditionally complete linear
order), the monotone case: the assumptions of Theorem 10.2.7 and (i) `g` increasing, (ii) `c`
decreasing, (iii) `x ↦ ∫ g dQ^X(·|x)` decreasing. If `ℙ_x(τ^* < ∞) = 1` for all `x`, the optimal
stopping time `τ^*` is of threshold type: `S_0` is an upper set — empty, all of `E`, or
`{x > x^*} ⊆ S_0 ⊆ {x ≥ x^*}` for a threshold `x^*` (Remark 10.1.6). -/
theorem corollary_10_2_8 {E : Type*} [MeasurableSpace E] [ConditionallyCompleteLinearOrder E]
    (P : StationaryProblem E) (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr)
    (hB : P.AssumptionB Pr) (S0 : Set E)
    (hS0 : S0 = {x : E | (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (P.g y : EReal)) ≤ (P.g x : EReal)})
    (hclosed : ∀ x ∈ S0, P.QX x S0 = 1)
    (hg : Monotone P.g) (hc : Antitone P.c)
    (hQg : Antitone fun x => erealIntegral (P.QX x) (fun y => (P.g y : EReal)))
    (hfin : ∀ x : E, Pr x {w | hitTime S0 w = ⊤} = 0) :
    IsUpperSet S0 ∧
    (S0 = ∅ ∨ S0 = Set.univ ∨
      ∃ xstar : E, {x : E | xstar < x} ⊆ S0 ∧ S0 ⊆ {x : E | xstar ≤ x}) ∧
    P.IsOptimal Pr (hitTime S0) := by sorry

end MDPFinance.OptimalStopping
