-- Prove2me | Theorems.Thm_MatrixSpencer_eq_C_7_C_9
-- name    : MatrixSpencer.eq_C_7_C_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:53.97504+00:00
-- url     : https://prove2.me/theorems/79331046-c896-4eae-8ba8-075c82331dc7
-- title:
--   Eqs. (C.7)–(C.9), pp.28–29 — scalar divided-difference bounds for $r_p^\prime$ and $v^\prime$
-- statement:
--   Let $p\ge2$ and $\alpha\ge\beta>0$, and let $x,y\in(-1,1)$. Then
--
--   $$(r_p')^{[1]}(x,y)\ge\frac12\max\{|x|,|y|\}^{2p-2}(\ell')^{[1]}(x,y),$$
--   $$(v')^{[1]}(x,y)\ge\frac\beta{(1-x)(1-y)},$$
--
--   and, if $\max\{|x|,|y|\}\ge3/4$,
--
--   $$(v')^{[1]}(x,y)\ge\frac\Gamma{(1-x)(1-y)},\qquad\Gamma=\frac\alpha2(3/4)^{2p-2}.$$
--
--   These are the scalar inputs of the curvature bound, through Lemma C.1.
--
--   Differences from the source:
--   - generalization: the standing assumption (2.2) of the section → only p ≥ 2 and α ≥ β > 0; reason: the page's derivation uses nothing else; (2.2) implies these
--   - encoding: q and r_q in Step 1–3 and Appendix C → p and r_p; reason: the same integer; the page uses both letters
--   - encoding: "The case x = y follows by continuity" → at x = y the bound is on the second derivative, the value of the divided difference; reason: the definition of f′^[1] on p.27
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Lemma 2.6, Step 2, (C.7) p.28 (PDF p.30), (C.8), (C.9) p.29 (PDF p.31)

import Mathlib
import Definitions.Def_MatrixSpencer_ell
import Definitions.Def_MatrixSpencer_tailR
import Definitions.Def_MatrixSpencer_vPot
import Definitions.Def_MatrixSpencer_divDiff

namespace MatrixSpencer

/-- **The scalar divided-difference bounds (C.7), (C.8), (C.9), proof of Lemma 2.6, Step 2.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Lemma 2.6, p.28 (PDF p.30): "(r′_q)^[1](x, y) ≥ ½ max{|x|, |y|}^{2q−2}(ℓ′)^[1](x, y), x, y ∈ (−1, 1).
(C.7)"; p.29 (PDF p.31): "(v′)^[1](x, y) ≥ β/((1 − x)(1 − y)), for all x, y ∈ (−1, 1), (C.8)", "(v′)^[1](x, y) ≥
Γ/((1 − x)(1 − y)), for max{|x|, |y|} ≥ 3/4, (C.9) where Γ = (α/2)(3/4)^{2q−2}".

**Formalization Note.** `p` is the page's `q`. `f′^[1]` is `divDiff f`; at `x = y` this is `f″`, which is
what the page's "by continuity" gives. Only `p ≥ 2` and `α ≥ β > 0` of (2.2) are assumed. -/
theorem eq_C_7_C_9 (α β : ℝ) (p : ℕ) (hp : 2 ≤ p) (hαβ : β ≤ α) (hβ : 0 < β)
    (x y : ℝ) (hx : |x| < 1) (hy : |y| < 1) :
    (1 / 2) * (max |x| |y|) ^ (2 * p - 2) * divDiff ell x y ≤ divDiff (tailR p) x y ∧
    β / ((1 - x) * (1 - y)) ≤ divDiff (vPot α β p) x y ∧
    (3 / 4 ≤ max |x| |y| →
      ((α / 2) * (3 / 4 : ℝ) ^ (2 * p - 2)) / ((1 - x) * (1 - y)) ≤
        divDiff (vPot α β p) x y) := by sorry

end MatrixSpencer
