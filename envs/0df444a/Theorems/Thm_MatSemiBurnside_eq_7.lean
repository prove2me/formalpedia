-- Prove2me | Theorems.Thm_MatSemiBurnside_eq_7
-- name    : MatSemiBurnside.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:00.655178+00:00
-- url     : https://prove2.me/theorems/5e00b39d-03b8-4c81-9d83-97fafc0a0d65
-- title:
--   Eq. (7): $\operatorname{rank}(ab)=r-\dim(\operatorname{im}(a)\cap\ker(b))$
-- statement:
--   Let $d$ be a positive integer and $r\in\mathbb N$, and let $a,b\in\mathrm{Mat}_d(\mathbb Q)$ both have rank $r$. With kernels and images taken for the row action $x\mapsto xa$,
--   $$\operatorname{rank}(ab)=r-\dim\big(\operatorname{im}(a)\cap\ker(b)\big).$$
--
--   This formula turns the question whether a product preserves rank into an intersection test on subspaces; it underlies Claim A.2.
--
--   Differences from the source:
--   - encoding: dim(im(a) ∩ ker(b)) and the difference r − dim(…) → `Module.finrank ℚ ↥(rowIm a ⊓ rowKer b)` and subtraction in ℕ; reason: im(a) ∩ ker(b) is a subspace of im(a), of dimension at most r, so the ℕ subtraction is never truncated
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix A, eq. (7), p.29

import Mathlib
import Definitions.Def_MatSemiBurnside_rowKer
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Eq. (7).** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix A, eq. (7), p.29: "For rank-r matrices a, b, restriction of b to im(a)
gives rank(ab) = r − dim(im(a) ∩ ker(b))."

**Formalization Note.** Kernels and images are those of the row action `x ↦ xa`. The subtraction is
in ℕ; `im(a) ∩ ker(b)` is a subspace of `im(a)`, of dimension at most r, so it is never truncated. -/
theorem eq_7 {d : ℕ} (hd : 0 < d) (r : ℕ) (a b : Matrix (Fin d) (Fin d) ℚ) (ha : a.rank = r) (hb : b.rank = r) :
    (a * b).rank = r - Module.finrank ℚ ↥(rowIm a ⊓ rowKer b) := by sorry

end MatSemiBurnside
