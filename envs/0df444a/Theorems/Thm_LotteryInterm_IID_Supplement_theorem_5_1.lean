-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_theorem_5_1
-- name    : LotteryInterm.IID.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:11:18.62014+00:00
-- url     : https://prove2.me/theorems/7867f696-c877-4456-a2ec-4dd73b0e7f94
-- title:
--   Theorem 5.1 — in the message-dependent model randomized menus do no better than a posted price
-- statement:
--   Let $n\ge1$ bidders have independent regular values satisfying $v\Pr[V>v]\to0$, with $\mathrm{OPT}>0$. Let $\mathcal O$ be any seller menu — possibly infinite, containing $(0,0)$, with a utility-maximizing option for every type. In the message-dependent model the intermediary may choose both which bidder to forward and which option (or lottery of options) to forward. Then there is a posted price $p\ge0$ such that
--   $$\mathrm{RandMD}(\mathcal O)\ \le\ \mathrm{DET}(p),$$
--   where $\mathrm{RandMD}(\mathcal O)$ is the seller's revenue against the intermediary's best responses (worst case, as for $\mathrm{RandMI}$) and $\mathrm{DET}(p)$ is the seller's revenue from posting $p$.
--
--   This contrasts with the message-independent model of the published mission, where two-price lotteries strictly help the seller.
--
--   Differences from the source:
--   - encoding: a menu {(alpha_j, beta_j) : j in J}, J any index set, each buyer having a utility-maximizing choice → GenMenu: a set of options in [0,1] x [0, infinity) containing (0,0) with a maximizer for every real type; reason: the proviso of p.15; for negative types the outside option is always a maximizer, so the extra types add no condition
--   - encoding: the message-dependent intermediary auction (y, q) forwarding bidder i's message → per bidder: selection probability y_i, (allocation, seller payment) = y_i times a point of the convex hull of the options, and a fee q_i, BIC and interim IR; reason: revelation principle; the mean of a lottery over options lies in the convex hull of the options and every hull point is a finite lottery
--   - reading: 'given that the revenue-maximizing intermediary always best responds', RandMD(MS) → RandMD is the infimum of the seller's revenue over every message-dependent best response, minus infinity if none exists; reason: Assumption 3.2 resolves intermediary ties against the seller, as for the published RandMI; the inequality holds trivially exactly when the source's hypothesis that a best response exists fails
--   - encoding: DET(p) for the posted price p → the published message-independent RandMI at postedPrice p; reason: §2.2: for a posted price the two models coincide
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - encoding: regular distribution with a PDF on its support [a, b] (Definition A.2 with alpha = 0) → the published ValueDist (density positive on (a, b), optional terminal atom, phi(b) = b) with Regular asking phi nondecreasing on (a, b]; reason: the density value at the single point a does not change the law; the two classes of laws coincide (same encoding as the published mission)
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 5.1, p.15 (PDF p.16); Lemma 5.2 and proofs, pp.15–16 (PDF pp.16–17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Supplement_MessageDependent

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Theorem 5.1: in the message-dependent model randomization does not help the
seller: for every (possibly infinite) menu some posted price does at least as well. -/
theorem theorem_5_1 {n : ℕ} (hn : 0 < n) (D : Fin n → ValueDist)
    (hreg : ∀ i, Regular (D i)) (htail : ∀ i, VanishingTail (D i))
    (hopt : 0 < OPT D) (O : GenMenu) :
    ∃ (p : ℝ) (hp : 0 ≤ p), RandMD D O ≤ RandMI D (postedPrice p hp) := by sorry

end LotteryInterm.IID.Supplement
