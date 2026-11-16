-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_corollary_A_4
-- name    : LotteryInterm.IID.Supplement.corollary_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:07:59.45651+00:00
-- url     : https://prove2.me/theorems/7ca439b9-5a38-456a-bf89-8ce741b376b9
-- title:
--   Corollary A.4 — $\Pr[\phi(v)\ge p]\ge c_\alpha\Pr[v\ge p]$ for α-strongly regular laws
-- statement:
--   Let $D$ be an α-strongly regular value law with $0<\alpha\le1$, support $[a,b]$ and virtual value $\phi$, and let $c_\alpha=\alpha^{1/(1-\alpha)}$ for $\alpha<1$, $c_1=1/e$. For every price $p$ in the support, $a\le p\le b$,
--   $$\Pr_{v\sim D}[\phi(v)\ge p]\ \ge\ c_\alpha\,\Pr_{v\sim D}[v\ge p].$$
--
--   This is the form of the corollary used in the proof of Theorem 4.2: a constant fraction of the bidders above any price also have virtual value above it.
--
--   Differences from the source:
--   - reading: two equivalent forms: Pr[v >= phi^{-1}(p) | v >= p] >= c_alpha, 'in other words' Pr[phi(v) >= p] >= c_alpha Pr[v >= p] → the second form; reason: it needs no inverse of phi (which may be flat or jump) and is the form Theorem 4.2's proof uses
--   - reading: p in the support of F → lo <= p <= hi; reason: Definition A.2 calls [a, b] the support
--   - encoding: alpha-strongly regular: phi(y) - phi(x) >= alpha (y - x) for all a <= x <= y <= b (Definition A.2) → StronglyRegular alpha D on the published ValueDist, asked for lo < x <= y <= hi; reason: the same set as the published Regular; the lowest point a is a null type whose density may vanish, and alpha = 0 gives exactly Regular
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Corollary A.4, p.37 (PDF p.38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Supplement_StrongRegularity

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Corollary A.4, "in other words" form: for an α-strongly regular law and every
price `p` in the support `[lo, hi]`, `Pr[ϕ(v) ≥ p] ≥ c_α · Pr[v ≥ p]`. -/
theorem corollary_A_4 (D : ValueDist) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsr : StronglyRegular α D) (p : ℝ) (hlo : D.lo ≤ p) (hhi : (p : WithTop ℝ) ≤ D.hi) :
    cAlpha α * (D.law {v | p ≤ v}).toReal ≤ (D.law {v | p ≤ virtualValue D v}).toReal := by sorry

end LotteryInterm.IID.Supplement
