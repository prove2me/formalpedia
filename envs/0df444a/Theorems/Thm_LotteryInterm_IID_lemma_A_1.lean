-- Prove2me | Theorems.Thm_LotteryInterm_IID_lemma_A_1
-- name    : LotteryInterm.IID.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:08.450399+00:00
-- url     : https://prove2.me/theorems/1f56ece5-d259-4378-837d-93addeb38f7d
-- title:
--   Lemma A.1 — virtual values after a nonnegative shift
-- statement:
--   Let $F$ have density $f$ and virtual value $\phi$, and let $G_p$ be the law of $(V-p)^+$ for $V\sim F$ and $p\ge0$. At every $v\ge p$ in the nonterminal support where $f(v)>0$, the shifted density-version virtual value satisfies
--   $$\psi(v-p)=\phi(v)-p.$$
--   If the support has a finite terminal endpoint $H>p$, the same identity holds there under $\phi(H)=H$ and $\psi(H-p)=H-p$.
--
--   Both clauses are retained, including the atom of the shifted law at zero. This is the virtual-value translation used to analyze the posted-price intermediary and shifted benchmarks.
--
--   Differences from the source:
--   - encoding: virtual-value density formula where defined → the nonterminal identity requires support membership and positive density; reason: division by a zero density is not the source formula; the terminal clause has no density restriction
--   - generalization: standing regularity, tail condition, and positive OPT → the identity holds for every represented law; reason: both clauses are algebraic and require none of these standing assumptions
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Lemma A.1, p.37 (PDF p.38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Myerson

open MeasureTheory

namespace LotteryInterm.IID

/-- Both the density identity and the finite terminal-atom identity. -/
theorem lemma_A_1 (D : ValueDist) (p : ℝ) (hp : 0 ≤ p) :
    (∀ v : ℝ, p ≤ v → D.lo ≤ v → (v : WithTop ℝ) < D.hi →
      0 < D.density v →
      shiftedVirtual D p (v - p) = virtualValue D v - p) ∧
    (∀ H : ℝ, D.hi = (H : WithTop ℝ) → p < H →
      shiftedVirtual D p (H - p) = virtualValue D H - p) := by sorry

end LotteryInterm.IID
