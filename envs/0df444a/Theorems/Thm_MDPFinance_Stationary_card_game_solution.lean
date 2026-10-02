-- Prove2me | Theorems.Thm_MDPFinance_Stationary_card_game_solution
-- name    : MDPFinance.Stationary.card_game_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:46:39.05737+00:00
-- url     : https://prove2.me/theorems/960c29f5-c9ea-4272-a3d0-ae5ef79fcc47
-- title:
--   Theorem 2.6.1 — the red-and-black card game
-- statement:
--   In the red-and-black card game — a deck of $b_0$ black and $r_0$ red cards is uncovered one
--   at a time; the player may stop at any point and wins/loses one Euro according to the colour
--   of the next card — modeled as the stationary Markov Decision Model of §2.6.1 with
--   state $(b,r)$ = cards remaining, action "go ahead"/"stop", the transition densities of
--   Eq. (2.1), reward and terminal reward both $(b-r)/(b+r)$ when stopping (zero for "go ahead"),
--   and $\beta = 1$: the maximal value is $J_{r_0+b_0}(b_0,r_0) = g(b_0,r_0) =
--   (b_0-r_0)/(b_0+r_0)$, and **every** strategy is optimal — no policy does better than stopping
--   immediately.
--
--   **Formalization Note.** The model's exact transition/reward/terminal-reward data are given as
--   hypotheses on an abstract `StationaryMarkovDecisionModel (ℕ × ℕ) Bool` (matching the book's
--   own discrete-density convention `q(x'\mid x,a) := Q(\{x'\}\mid x,a)`, introduced in the text
--   following Theorem 2.5.4) rather than built via an explicit `PMF`/`Kernel` construction. The
--   "every strategy is optimal" conclusion is the universally-quantified third conjunct — not
--   weakened to the existence of an optimal strategy, which is the book's own emphasized point.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 46, PDF 61, Theorem 2.6.1

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators
import Definitions.Def_MDPFinance_Stationary_ValueFunction

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

/-- Theorem 2.6.1 (Bäuerle–Rieder, p. 46, PDF 61), the red-and-black card game. `M` is the
stationary Markov Decision Model of §2.6.1 (p. 44-45, PDF 59-60): state space `E := ℕ × ℕ`
(the pair `(b,r)` of remaining black/red cards, `(0,0)` absorbing), action space `A := Bool`
(`false` = "go ahead", `true` = "stop"), `D(x) = A` except `D(0,1) = D(1,0) = {true}`, kernel
density (Eq. 2.1) `q((b,r-1)\mid(b,r),\mathrm{false}) = r/(r+b)` (`r ≥ 1`),
`q((b-1,r)\mid(b,r),\mathrm{false}) = b/(r+b)` (`b ≥ 1`), `q((0,0)\mid x,\mathrm{true}) = 1`,
`q((0,0)\mid(0,0),a) = 1`; reward `r(x,\mathrm{true}) = (b-r)/(b+r)` for `x = (b,r) ≠ (0,0)`,
zero otherwise; terminal reward `g` the same formula, `g(0,0) = 0`; `β := 1`. Then the maximal
value of the card game is `J_{r_0+b_0}(b_0,r_0) = g(b_0,r_0) = (b_0-r_0)/(b_0+r_0)`, and every
strategy is optimal. -/
theorem card_game_solution (M : StationaryMarkovDecisionModel (ℕ × ℕ) Bool)
    (hD : ∀ x a, (x, a) ∈ M.D ↔ (x ≠ (0, 1) ∧ x ≠ (1, 0)) ∨ a = true)
    (hQ_red : ∀ b r : ℕ, 1 ≤ r → M.Q ((b, r), false) {(b, r - 1)} = ENNReal.ofReal (r / (r + b) : ℝ))
    (hQ_black : ∀ b r : ℕ, 1 ≤ b →
      M.Q ((b, r), false) {(b - 1, r)} = ENNReal.ofReal (b / (r + b) : ℝ))
    (hQ_stop : ∀ x : ℕ × ℕ, M.Q (x, true) {((0 : ℕ), (0 : ℕ))} = 1)
    (hQ_absorb : ∀ a : Bool, M.Q (((0 : ℕ), (0 : ℕ)), a) {((0 : ℕ), (0 : ℕ))} = 1)
    (hr_stop : ∀ b r : ℕ, (b, r) ≠ (0, 0) →
      M.r ((b, r), true) = ((b : ℝ) - (r : ℝ)) / ((b : ℝ) + (r : ℝ)))
    (hr_stop_G : M.r (((0 : ℕ), (0 : ℕ)), true) = 0)
    (hr_go : ∀ x : ℕ × ℕ, M.r (x, false) = 0)
    (hg : ∀ b r : ℕ, (b, r) ≠ (0, 0) → M.g (b, r) = ((b : ℝ) - (r : ℝ)) / ((b : ℝ) + (r : ℝ)))
    (hg_G : M.g (0, 0) = 0)
    (hβ : M.β = 1) (b0 r0 : ℕ) :
    J M (r0 + b0) (b0, r0) = (M.g (b0, r0) : EReal) ∧
      M.g (b0, r0) = ((b0 : ℝ) - (r0 : ℝ)) / ((b0 : ℝ) + (r0 : ℝ)) ∧
      ∀ π : ℕ → (ℕ × ℕ) → Bool, IsPolicySeq M (r0 + b0) π →
        Jpi M π (r0 + b0) (b0, r0) = J M (r0 + b0) (b0, r0) := by sorry

end MDPFinance.Stationary
