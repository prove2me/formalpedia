-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_theorem_4_3
-- name    : LotteryInterm.IID.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:09:36.387913+00:00
-- url     : https://prove2.me/theorems/f1f1bc79-2d4c-4903-8615-ab8cca1e5912
-- title:
--   Theorem 4.3 (corrected: $p^*$ not an atom) — posting the optimal anonymous price earns $c_\alpha$, $c_\alpha(1-1/e)$, $c_\alpha/2.63$ of OPT
-- statement:
--   Let $n\ge1$ bidders have independent values $v_i\sim D_i$, each α-strongly regular with $0<\alpha\le1$, with $\mathrm{OPT}>0$. Let $p^*\ge0$ be an optimal anonymous posted price without an intermediary, $p^*\Pr[\exists i,\ v_i\ge p^*]=\mathrm{APRev}$, such that no bidder has an atom at $p^*$: $\Pr[\exists i,\ v_i=p^*]=0$. Let $\mathrm{DET}(p^*)$ be the seller's revenue from posting $p^*$ against a revenue-maximizing intermediary (worst case over its best responses). Then
--   1. if $n=1$: $\ \mathrm{DET}(p^*)\ge c_\alpha\,\mathrm{OPT}$;
--   2. if all bidders are identically distributed: $\ \mathrm{DET}(p^*)\ge c_\alpha(1-1/e)\,\mathrm{OPT}$;
--   3. in general: $$\mathrm{DET}(p^*)\ \ge\ \frac{c_\alpha}{2.63}\,\mathrm{OPT}.$$
--
--   As printed, the theorem omits the no-atom condition and is then false: for one bidder with the law $F_{\alpha,H}$ of equation (1) truncated at $H<1/\alpha$, the curve $p\Pr[v\ge p]$ increases on $[0,H]$, so $p^*=H$ is the terminal atom; posting $H$ leaves every access value $(v-H)^+=0$, the intermediary does not sell (Assumption 3.2), and $\mathrm{DET}(H)=0<c_\alpha\mathrm{OPT}$. The added condition changes nothing when $p^*$ is not an atom.
--
--   Differences from the source:
--   - correction: AP* is any optimal anonymous posted price → AP* is an optimal anonymous posted price with Pr[exists i, v_i = AP*] = 0; reason: counterexample satisfying every assumption: n = 1, F_{alpha,H} of (1) truncated at H < 1/alpha is bounded and alpha-strongly regular, p Pr[v >= p] = p(1+(1-alpha)p)^{-1/(1-alpha)} increases on [0, H] (log-derivative sign 1 - alpha p), so AP* = H; at price H the access law is a point mass at 0, Assumption 3.2 forbids a sale, DET(H) = 0 < c_alpha OPT
--   - encoding: ratio DET(p*)/OPT >= k → k * OPT <= RandMI at postedPrice p*; reason: OPT is positive, so the two forms agree
--   - reading: n i.i.d. bidders → any n >= 1 with all laws (D i).law equal; reason: identically distributed independent values
--   - encoding: 1/2.63 (footnote 14; C* approx 2.62 in Theorem A.11) → the real number 1/2.63; reason: printed constant
--   - encoding: DET(p), the seller's revenue at posted price p facing a revenue-maximizing intermediary under Assumptions 3.2/3.3 → the published RandMI at postedPrice p (infimum over every intermediary best response, minus infinity if none), and DET the supremum over p >= 0; reason: for a posted price every best response sells access almost surely where the access virtual value is positive, so the infimum is the Assumption 3.2 revenue
--   - generalization: Assumption 3.2 restricts intermediary tie-breaking → the guarantee holds against every revenue-maximizing BIC/IR intermediary (RandMI is the infimum over all best responses); reason: a bound on all best responses implies the bound on the source subclass
--   - encoding: the intermediary is presumed to best respond → RandMI is minus infinity when best responses are absent, and existence is stated explicitly in menu guarantees; reason: an empty best-response set cannot certify a guarantee
--   - encoding: independent nonnegative bidder values and expected revenues → Fin n, product probability measures, EReal optima, and measurable mechanisms with integrable payments and all report sections; reason: these represent the same stochastic auction; unbounded optima and undefined real integrals cannot default to zero
--   - encoding: Bayesian incentive compatibility and interim individual rationality → truthful inequalities for almost every original value against every real report; reason: null types do not affect revenue; reports outside the support extend the mechanism without changing its attainable revenues
--   - encoding: alpha-strongly regular: phi(y) - phi(x) >= alpha (y - x) for all a <= x <= y <= b (Definition A.2) → StronglyRegular alpha D on the published ValueDist, asked for lo < x <= y <= hi; reason: the same set as the published Regular; the lowest point a is a null type whose density may vanish, and alpha = 0 gives exactly Regular
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 4.3, pp.11–12 (PDF pp.12–13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Supplement_StrongRegularity
import Definitions.Def_LotteryInterm_IID_Intermediary

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Theorem 4.3 (corrected): at an optimal anonymous price `p*` that is not an atom of
any bidder's value, the intermediated seller posting `p*` earns `c_α · OPT` (one
bidder), `c_α (1 - 1/e) · OPT` (identically distributed bidders), and
`c_α (1/2.63) · OPT` (independent bidders). -/
theorem theorem_4_3 {n : ℕ} (hn : 0 < n) (D : Fin n → ValueDist) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hsr : ∀ i, StronglyRegular α (D i))
    (hopt : 0 < OPT D) (p : ℝ) (hAP : IsOptimalAnonymousPrice D p)
    (hnoatom : (prior D) {v | ∃ i, v i = p} = 0) :
    (n = 1 → ((cAlpha α : ℝ) : EReal) * OPT D ≤ RandMI D (postedPrice p hAP.1)) ∧
    ((∀ i j, (D i).law = (D j).law) →
      ((cAlpha α * (1 - Real.exp (-1)) : ℝ) : EReal) * OPT D ≤
        RandMI D (postedPrice p hAP.1)) ∧
    ((cAlpha α * (1 / 2.63) : ℝ) : EReal) * OPT D ≤ RandMI D (postedPrice p hAP.1) := by sorry

end LotteryInterm.IID.Supplement
