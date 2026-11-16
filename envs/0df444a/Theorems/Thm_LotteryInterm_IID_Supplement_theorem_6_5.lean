-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_theorem_6_5
-- name    : LotteryInterm.IID.Supplement.theorem_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:13:29.637944+00:00
-- url     : https://prove2.me/theorems/6f42661f-286b-47b7-a215-1b4ba9e199de
-- title:
--   Theorem 6.5 — α-strongly regular bidders: a two-price lottery guarantees $(\sqrt\alpha/96)\,\mathrm{OPT}$
-- statement:
--   Let $n\ge1$ bidders have independent, possibly non-identical α-strongly regular value laws with $0<\alpha\le1$ (unbounded supports allowed), and $\mathrm{OPT}>0$. Then $\mathrm{OPT}$ is finite and there are $0\le a\le b$ and $\lambda\in[0,1]$ such that the menu $M=M(a,b,\lambda)$ with at most two prices has an intermediary best response and
--   $$\mathrm{RandMI}(M)\ \ge\ \frac{\sqrt\alpha}{96}\,\mathrm{OPT}$$
--   against every revenue-maximizing intermediary.
--
--   The paper writes $\Omega(\sqrt\alpha)\,\mathrm{OPT}$; the proof yields $\sqrt\alpha/48$ for $\alpha\le1/4$ ($q=\sqrt\alpha$, Lemma 6.2 with $H=T$, $\log(2T/\mathrm{OPT})<12/q$) and, for $\alpha>1/4$, the $\alpha=1/4$ mechanism, giving $\mathrm{OPT}/96$; hence $\sqrt\alpha/96$ for all $0<\alpha\le1$. Unlike Theorem 6.4 the guarantee does not degrade with $n$.
--
--   Differences from the source:
--   - generalization: RandMI(M'S) = Omega(sqrt alpha) OPT → the explicit coefficient sqrt(alpha)/96; reason: the printed proof gives sqrt(alpha)/48 for alpha <= 1/4 and OPT/96 >= sqrt(alpha) OPT/96 for alpha > 1/4 (an alpha-strongly regular law is 1/4-strongly regular); no epsilon appears in this proof
--   - reading: a mechanism using at most two prices → the published twoPrice menu (equal prices and endpoint weights allowed); reason: includes posted prices, as Lemma 6.2 requires
--   - encoding: finite positive OPT → finiteness is a conclusion; reason: it follows from the hypotheses
--   - generalization: Assumption 3.2 restricts intermediary tie-breaking → the guarantee holds against every revenue-maximizing BIC/IR intermediary (RandMI is the infimum over all best responses); reason: a bound on all best responses implies the bound on the source subclass
--   - encoding: the intermediary is presumed to best respond → RandMI is minus infinity when best responses are absent, and existence is stated explicitly in menu guarantees; reason: an empty best-response set cannot certify a guarantee
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - encoding: alpha-strongly regular: phi(y) - phi(x) >= alpha (y - x) for all a <= x <= y <= b (Definition A.2) → StronglyRegular alpha D on the published ValueDist, asked for lo < x <= y <= hi; reason: the same set as the published Regular; the lowest point a is a null type whose density may vanish, and alpha = 0 gives exactly Regular
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 6.5, p.23 (PDF p.24); proof pp.23–25 (PDF pp.24–26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Supplement_StrongRegularity
import Definitions.Def_LotteryInterm_IID_Intermediary

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Theorem 6.5: independent α-strongly regular bidders; a menu with at most two
prices has a best response and guarantees `(√α / 96) · OPT` against every best
response. -/
theorem theorem_6_5 {n : ℕ} (hn : 0 < n) (D : Fin n → ValueDist) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hsr : ∀ i, StronglyRegular α (D i))
    (hopt : 0 < OPT D) :
    OPT D < ⊤ ∧
    ∃ (a b weight : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hw : weight ∈ Set.Icc 0 1),
      let M := twoPrice a b weight ha hab hw
      (∃ I, BestResponse D M I) ∧
      ((Real.sqrt α / 96 : ℝ) : EReal) * OPT D ≤ RandMI D M := by sorry

end LotteryInterm.IID.Supplement
