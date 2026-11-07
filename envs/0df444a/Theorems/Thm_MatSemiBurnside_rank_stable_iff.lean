-- Prove2me | Theorems.Thm_MatSemiBurnside_rank_stable_iff
-- name    : MatSemiBurnside.rank_stable_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:39:22.534193+00:00
-- url     : https://prove2.me/theorems/824d668f-4957-4e8d-8035-afb7d7a3e4ef
-- title:
--   Claim A.2 (last sentence): rank-stable iff $\ker(a)\cap\operatorname{im}(a)=\{0\}$
-- statement:
--   Let $d$ be a positive integer. A matrix $a\in\mathrm{Mat}_d(\mathbb Q)$ is rank-stable, that is $\operatorname{rank}(a)=\operatorname{rank}(a^2)$, if and only if
--   $$\ker(a)\cap\operatorname{im}(a)=\{0\},$$
--   with kernel and image taken for the row action $x\mapsto xa$.
--
--   This characterisation is what makes the sets $S_{K,U}$ of matrices with a common kernel $K$ and image $U$, $K\cap U=\{0\}$, stable subsemigroups in the proof of Claim 3.2.
--
--   Differences from the source: none.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix A, Claim A.2 (last sentence), p.29

import Mathlib
import Definitions.Def_MatSemiBurnside_IsStableSet
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Rank-stable iff kernel and image meet trivially.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix A, Claim A.2 (last sentence),
p.29: "A matrix is rank-stable exactly when its kernel and image have intersection {0}."

**Formalization Note.** Row action kernel and image; `{0}` is the zero submodule `⊥`. -/
theorem rank_stable_iff {d : ℕ} (hd : 0 < d) (a : Matrix (Fin d) (Fin d) ℚ) :
    IsRankStable a ↔ rowKer a ⊓ rowIm a = ⊥ := by sorry

end MatSemiBurnside
