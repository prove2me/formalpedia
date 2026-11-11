-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_appendix_B
-- name    : FracColorLocal.KrFree.appendix_B
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:12:13.890194+00:00
-- url     : https://prove2.me/theorems/7549adfe-dbd3-4fb5-9f17-8e7d156999dd
-- title:
--   Appendix B — Pinsker's inequality for probability vectors: ‖p − q‖_TV ≤ √(KL(p‖q)/2)
-- statement:
--   For probability vectors $p,q$ on a finite set,
--
--   $$\|p-q\|_{\mathrm{TV}}=\frac12\sum_y|p(y)-q(y)|\ \le\ \sqrt{\mathrm{KL}(p\|q)/2},$$
--
--   where $\mathrm{KL}(p\|q)=\sum_yp(y)\log(p(y)/q(y))$ (terms with $p(y)=0$ are zero) and $\mathrm{KL}(p\|q)=+\infty$ if $p(y)>0=q(y)$ for some $y$. It converts the entropy increments of Lemma 8.2 into total-variation bounds.
--
--   Differences from the source:
--   - encoding: the case $\mathrm{KL}(p\|q)=+\infty$ (where the right side is $+\infty$ and the claim is immediate) → excluded by the hypothesis `klDiv p q ≠ ⊤`, and $\sqrt{\cdot}$ is taken of the real value; reason: $\sqrt{+\infty}$ is not a real number; the excluded case is trivially true in the source.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 50 (PDF 51), Appendix B

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_Entropy

namespace FracColorLocal.KrFree

/-- Appendix B (Pinsker's inequality, finite form): for probability vectors `p, q` on a finite set,
`‖p - q‖_TV ≤ √(KL(p ‖ q)/2)`; the case `KL(p ‖ q) = +∞` is trivial and is excluded. -/
theorem appendix_B {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp0 : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1) (hq0 : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (hfin : klDiv p q ≠ ⊤) :
    tvDist p q ≤ Real.sqrt ((klDiv p q).toReal / 2) := by sorry

end FracColorLocal.KrFree
