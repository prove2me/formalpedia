-- Prove2me | Theorems.Thm_LotteryInterm_IID_few_high_values
-- name    : LotteryInterm.IID.few_high_values
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:30.294034+00:00
-- url     : https://prove2.me/theorems/045489f1-942a-4490-8188-d61995a9582e
-- title:
--   §6.2.1 — probability of a high bidder value
-- statement:
--   For $n\ge1$ independent regular bidders with vanishing tails and $\operatorname{OPT}>0$, every $\tau>0$ satisfies
--   $$\tau\Pr[\max_i v_i\ge\tau]\le\operatorname{OPT}.$$
--   Consequently $\operatorname{OPT}$ is finite and
--   $$\Pr[\max_i v_i\ge2\operatorname{OPT}]\le\tfrac12.$$
--   This is the high-value probability bound used in the proof of Theorem 6.3. The statement retains the displayed specialization and gives the reserve-auction inequality for every positive threshold.
--
--   Differences from the source:
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: finite positive optimal revenue in the numerical cutoff formulas → finiteness is a conclusion and the real cutoff uses EReal.toReal; reason: regularity and the vanishing-tail assumption imply finiteness; finiteness is never assumed as a replacement for those facts
--   - generalization: the display uses iid laws and tau equal to twice OPT → independent nonidentical laws and every positive threshold; reason: the reserve-auction bound applies without identical distributions and includes the displayed case
--   - encoding: regular distribution with a PDF on its support [a, b]: phi(y) - phi(x) >= 0 for all a <= x <= y <= b (Definition A.2) → ValueDist with density positive on (a, b) and an optional terminal atom; Regular asks phi nondecreasing on (a, b]; reason: the density value at the single point a does not change the law, and with f(a) = 0 the source formula gives phi(a) = -infinity, which meets the monotonicity at a; a zero density inside (a, b) would make phi = -infinity at an interior point, which regularity excludes; the two classes of laws coincide
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), §6.2.1, proof of Theorem 6.3, p.20 (PDF p.21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Myerson

open MeasureTheory

namespace LotteryInterm.IID

/-- The reserve-auction display in §6.2.1, for every positive cutoff, and its
specialization at twice the optimal revenue. -/
theorem few_high_values {n : ℕ} (hn : 0 < n) (D : Fin n → ValueDist)
    (hreg : ∀ i, Regular (D i)) (htail : ∀ i, VanishingTail (D i))
    (hopt : 0 < OPT D) :
    OPT D < ⊤ ∧
    (∀ τ : ℝ, 0 < τ →
      ((τ * (prior D {v | ∃ i, τ ≤ v i}).toReal : ℝ) : EReal) ≤ OPT D) ∧
    (prior D {v | ∃ i, 2 * (OPT D).toReal ≤ v i}).toReal ≤ 1 / 2 := by sorry

end LotteryInterm.IID
