-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_theorem_4_2
-- name    : LotteryInterm.IID.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:08:45.999197+00:00
-- url     : https://prove2.me/theorems/b609abba-15c7-4076-a788-89d2fafcec77
-- title:
--   Theorem 4.2 — the intermediated deterministic seller earns $c_\alpha\cdot\mathrm{APRev}$
-- statement:
--   Let $n\ge1$ bidders have independent values $v_i\sim D_i$, each $D_i$ α-strongly regular with $0<\alpha\le1$, and suppose the optimal revenue $\mathrm{OPT}$ is positive. Let $\mathrm{APRev}$ be the best revenue of an anonymous posted price without an intermediary, and $\mathrm{DET}$ the best revenue of a seller who posts a price $p$ and faces a revenue-maximizing intermediary that resells access to the posted price (the published $\sup_{p\ge0}\mathrm{RandMI}(\text{price }p)$). Then
--   $$\mathrm{DET}\ \ge\ c_\alpha\,\mathrm{APRev},\qquad c_\alpha=\alpha^{1/(1-\alpha)}\ (\alpha<1),\quad c_1=1/e .$$
--   The laws need not be identical, and no bound on the supports is assumed.
--
--   Together with Theorem 4.4 this shows that the factor $c_\alpha$ is the right dependence on $\alpha$ for deterministic sellers.
--
--   Differences from the source:
--   - reading: there is an anonymous posted price mechanism that guarantees DET >= c_alpha APRev → the displayed inequality with DET the supremum over posted prices of the intermediated seller's revenue; reason: §3.1 defines DET as the maximum deterministic revenue; the price p* of the proof need not attain it (Theorem 4.3's correction exhibits p* with DET(p*) = 0), so no particular attaining price is asserted
--   - encoding: DET(p), the seller's revenue at posted price p facing a revenue-maximizing intermediary under Assumptions 3.2/3.3 → the published RandMI at postedPrice p (infimum over every intermediary best response, minus infinity if none), and DET the supremum over p >= 0; reason: for a posted price every best response sells access almost surely where the access virtual value is positive, so the infimum is the Assumption 3.2 revenue
--   - generalization: Assumption 3.2 restricts intermediary tie-breaking → the guarantee holds against every revenue-maximizing BIC/IR intermediary (RandMI is the infimum over all best responses); reason: a bound on all best responses implies the bound on the source subclass
--   - encoding: the intermediary is presumed to best respond → RandMI is minus infinity when best responses are absent, and existence is stated explicitly in menu guarantees; reason: an empty best-response set cannot certify a guarantee
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - encoding: alpha-strongly regular: phi(y) - phi(x) >= alpha (y - x) for all a <= x <= y <= b (Definition A.2) → StronglyRegular alpha D on the published ValueDist, asked for lo < x <= y <= hi; reason: the same set as the published Regular; the lowest point a is a null type whose density may vanish, and alpha = 0 gives exactly Regular
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 4.2, p.11 (PDF p.12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Supplement_StrongRegularity
import Definitions.Def_LotteryInterm_IID_Intermediary

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Theorem 4.2: against a revenue-maximizing intermediary, the best anonymous
posted price earns at least `c_α · APRev` for independent α-strongly regular bidders. -/
theorem theorem_4_2 {n : ℕ} (hn : 0 < n) (D : Fin n → ValueDist) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hsr : ∀ i, StronglyRegular α (D i))
    (hopt : 0 < OPT D) :
    ((cAlpha α : ℝ) : EReal) * APRev D ≤ DET D := by sorry

end LotteryInterm.IID.Supplement
