-- Prove2me | Theorems.Thm_LotteryInterm_IID_theorem_A_8
-- name    : LotteryInterm.IID.theorem_A_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:06.64471+00:00
-- url     : https://prove2.me/theorems/a646298c-c459-431f-9fe6-ca7a64502051
-- title:
--   Theorem A.8 — Myerson revenue and optimal allocation
-- statement:
--   Let $n\ge1$ bidders have independent nonnegative value laws with densities, possible terminal atoms, and vanishing tails. For every admissible BIC/IR single-item mechanism $(y,q)$ whose virtual surplus is integrable,
--   $$\mathbb E\!\left[\sum_i q_i(v)\right]\le\mathbb E\!\left[\sum_i\phi_i(v_i)y_i(v)\right].$$
--   Equality holds when every bidder's canonical lowest-type interim utility is zero. If the laws are regular, the defined Myerson auction with critical-value payments is admissible, attains the optimum, and allocates to a bidder with highest strictly positive virtual value whenever one exists, almost surely. In particular the nonnegative maximum virtual value is integrable and
--   $$\operatorname{OPT}=\mathbb E[\max\{0,\max_i\phi_i(v_i)\}].$$
--   This identifies the independently defined revenue benchmark and supplies all three clauses of the source theorem.
--
--   Differences from the source:
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - reading: the lowest type has zero interim utility → zero essential lower-endpoint utility of the canonical BIC representative; reason: a.e.-BIC allows arbitrary values at a null lowest report; the canonical utility, unlike that arbitrary value, satisfies the payment identity
--   - encoding: expected virtual surplus → the first clause requires its integrability; regular optimal surplus integrability is concluded; reason: only defined real expectations are compared, without a bounded-support or finite-mean restriction
--   - encoding: highest strictly positive virtual-value allocation → a fixed lowest-index tie rule and allocation characterization almost surely; reason: null endpoint reports can be extended without changing the auction outcomes under the prior
--   - generalization: the standing convention OPT is positive → the revenue theorem also covers zero OPT; reason: none of its clauses requires a positive optimum
--   - encoding: regular distribution with a PDF on its support [a, b]: phi(y) - phi(x) >= 0 for all a <= x <= y <= b (Definition A.2) → ValueDist with density positive on (a, b) and an optional terminal atom; Regular asks phi nondecreasing on (a, b]; reason: the density value at the single point a does not change the law, and with f(a) = 0 the source formula gives phi(a) = -infinity, which meets the monotonicity at a; a zero density inside (a, b) would make phi = -infinity at an interior point, which regularity excludes; the two classes of laws coincide
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem A.8, pp.39–40 (PDF pp.40–41); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Myerson

open MeasureTheory

namespace LotteryInterm.IID

/-- All clauses of Myerson's revenue theorem, including existence and attainment.
ZeroLowestUtility uses the canonical lower utility of an a.e.-BIC mechanism. -/
theorem theorem_A_8 {n : ℕ} (hn : 0 < n) (D : Fin n → ValueDist)
    (htail : ∀ i, VanishingTail (D i)) :
    (∀ M : Mechanism n, Admissible D id M →
      Integrable (virtualSurplus D M) (prior D) →
      revenue (prior D) M ≤ ∫ v, virtualSurplus D M v ∂prior D ∧
      (ZeroLowestUtility D M →
        revenue (prior D) M = ∫ v, virtualSurplus D M v ∂prior D)) ∧
    ((∀ i, Regular (D i)) →
      Integrable (maxVirtual D) (prior D) ∧
      Admissible D id (myerson D 0) ∧
      revenue (prior D) (myerson D 0) = ∫ v, maxVirtual D v ∂prior D ∧
      OPT D = ((∫ v, maxVirtual D v ∂prior D : ℝ) : EReal) ∧
      (∀ᵐ v ∂prior D,
        ((∀ i, virtualValue (D i) (v i) ≤ 0) → ∀ i, (myerson D 0).allocation v i = 0) ∧
        ((∃ i, 0 < virtualValue (D i) (v i)) →
          ∃ i, (myerson D 0).allocation v i = 1 ∧
            0 < virtualValue (D i) (v i) ∧
            ∀ j, virtualValue (D j) (v j) ≤ virtualValue (D i) (v i)))) := by sorry

end LotteryInterm.IID
