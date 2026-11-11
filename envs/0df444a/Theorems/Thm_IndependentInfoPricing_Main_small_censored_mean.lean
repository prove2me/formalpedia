-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_small_censored_mean
-- name    : IndependentInfoPricing.Main.small_censored_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:33.962294+00:00
-- url     : https://prove2.me/theorems/52ba88c0-814a-4855-98b6-325c26bd1987
-- title:
--   Proposition 4.24 — One side has small censored mean
-- statement:
--   Let $\varepsilon>0$. There is a finite positive threshold $\Theta=40(R+\varepsilon)$. With $P^\Theta=\sum_i\min(v_i^+,\Theta)$ and $N^\Theta=\sum_i\min(v_i^-,\Theta)$, at most one of their means is at least $5\Theta/3$. After one global reflection of the law if necessary,
--
--   $$\mathbb EP^\Theta<\frac53\Theta,\qquad\mathbb EU_+\le\frac53\Theta,\qquad\mathbb EA\le\frac53.$$
--
--   The orientation is an existential choice of the whole distribution. It is not a type-dependent choice of benchmark. Existence of a finite threshold is retained as a conclusion rather than assumed via an extra finite-moment hypothesis. This controls the two positive-side estimates used in the approximation.
--
--   Differences from the source:
--   - generalization: continuously differentiable marginal densities in the upper-bound section → probability marginals with no atom at zero and finite monopoly-price attainment on occurring branches; reason: these intermediate arguments use product laws and branch revenues without differentiability; every source instance satisfies these hypotheses
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
--   - encoding: Theta=40(R+epsilon) → existence of a finite positive real Theta whose nonnegative extended embedding equals 40(R+epsilon); reason: retains the threshold while avoiding a default-zero conversion of a possibly infinite benchmark; its finiteness is a conclusion
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Proposition 4.24, printed pp.48–48 (PDF pp.50–50); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Analysis

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Proposition 4.24, pp.48–49 (PDF 50–51), (86); orientation is chosen globally. -/
theorem small_censored_mean {Q : ℕ} (F : Marginals (Fin Q)) (hF : BranchScope F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Θ : ℝ, 0 < Θ ∧ ENNReal.ofReal Θ = 40 * (benchmark (productLaw F) + ENNReal.ofReal ε) ∧
      ¬ (ENNReal.ofReal (5 * Θ / 3) ≤ censoredExpectation F true Θ ∧
         ENNReal.ofReal (5 * Θ / 3) ≤ censoredExpectation F false Θ) ∧
      ∃ flip : Bool, let G := if flip then reflectedMarginals F else F
        censoredExpectation G true Θ < ENNReal.ofReal (5 * Θ / 3) ∧
        signExpectation G (uPlus G Θ) ≤ ENNReal.ofReal (5 * Θ / 3) ∧
        signExpectation G (tailsPlus G Θ) ≤ (5 / 3 : ℝ≥0∞) := by sorry

end IndependentInfoPricing.Main
