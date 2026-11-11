-- Prove2me | Theorems.Thm_LotteryInterm_IID_theorem_4_1
-- name    : LotteryInterm.IID.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:02.635669+00:00
-- url     : https://prove2.me/theorems/73732a65-230f-433d-a3e0-191e534e1778
-- title:
--   Theorem 4.1 — posted-price intermediary best response
-- statement:
--   Let $n\ge1$ independent regular bidders satisfy the vanishing-tail condition, and let the seller post price $p\ge0$. The defined virtual-value auction with reserve $p$ and critical-value access fees is an intermediary best response. Its optimum revenue is
--   $$\operatorname{OptRev}(F,u_{\{(1,p)\}})=\mathbb E[\max\{0,\max_i\phi_i(v_i)-p\}].$$
--   The expectation is integrable. Its access winner has highest strictly positive shifted virtual value; fixed index tie-breaking applies between positive maximizers. This is the source's personalized reserve expressed in virtual-value units, with the corresponding threshold fee in access-value units.
--
--   The statement supplies an actual optimal auction rather than an unspecified optimal mechanism.
--
--   Differences from the source:
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - encoding: personalized reserve phi_i inverse of p minus p → highest virtual value exceeding p with critical-value payments; reason: weak regularity does not give a single-valued ordinary inverse
--   - reading: the proof sometimes writes a weak inequality at zero virtual surplus → no access is sold at zero shifted virtual surplus; reason: this follows the strict rule of Assumption 3.2; either zero-surplus choice preserves intermediary optimality
--   - generalization: standing positive OPT → zero OPT is allowed too; reason: the best-response characterization remains valid
--   - encoding: regular distribution with a PDF on its support [a, b]: phi(y) - phi(x) >= 0 for all a <= x <= y <= b (Definition A.2) → ValueDist with density positive on (a, b) and an optional terminal atom; Regular asks phi nondecreasing on (a, b]; reason: the density value at the single point a does not change the law, and with f(a) = 0 the source formula gives phi(a) = -infinity, which meets the monotonicity at a; a zero density inside (a, b) would make phi = -infinity at an interior point, which regularity excludes; the two classes of laws coincide
--   - reading: the revenue-maximizing intermediary's best response is to run Myerson's optimal auction with reserve phi_i^{-1}(p) - p → this auction is a best response, and the optimal intermediary revenue equals E[max{0, max_i phi_i(v_i) - p}]; reason: best responses are not unique (equal virtual values across bidders, and selling or not at zero shifted virtual value are both optimal), so "the" cannot mean uniqueness; the proof on p.10 shows exactly that this auction attains the optimum
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 4.1, p.10 (PDF p.11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Myerson

open MeasureTheory

namespace LotteryInterm.IID

/-- Positive access virtual surplus wins; no inverse of a weakly monotone
virtual-value function is assumed. The defined auction has threshold payments. -/
theorem theorem_4_1 {n : ℕ} (hn : 0 < n) (D : Fin n → ValueDist)
    (hreg : ∀ i, Regular (D i)) (htail : ∀ i, VanishingTail (D i))
    (p : ℝ) (hp : 0 ≤ p) :
    BestResponse D (postedPrice p hp) (myerson D p) ∧
    Integrable (fun v => max (maxVirtual D v - p) 0) (prior D) ∧
    OptRev D (accessUtility (postedPrice p hp)) =
      ((∫ v, max (maxVirtual D v - p) 0 ∂prior D : ℝ) : EReal) := by sorry

end LotteryInterm.IID
