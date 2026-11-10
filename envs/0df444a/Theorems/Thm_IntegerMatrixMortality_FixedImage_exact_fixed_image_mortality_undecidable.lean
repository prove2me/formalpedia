-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_exact_fixed_image_mortality_undecidable
-- name    : IntegerMatrixMortality.FixedImage.exact_fixed_image_mortality_undecidable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:48.789855+00:00
-- url     : https://prove2.me/theorems/89e297c0-4ca6-4dc1-aacf-e27ff2d64c6d
-- title:
--   Corollary 1.2 — Exactly 5798 fixed matrices and the 5799-matrix consequence
-- statement:
--   There exist a prime p, a fixed set G of exactly 5798 distinct nonsingular integer two-by-two matrices, each with determinant p or −p, and a fixed rational line L such that no total computable Boolean algorithm on the four signed entries decides mortality of G∪{R} for every nonzero rank-one integer R with rational image L. Consequently,
--
--   $$\text{mortality for sets of exactly }5799\text{ distinct integer }2\times2\text{ matrices is undecidable}.$$
--
--   Both undecidability clauses are asserted together. The second is stated on injective lists of four-entry encodings, an effective presentation of finite sets of exactly that size. No bound is imposed on entries, natural inputs or product lengths.
--
--   Differences from the source:
--   - encoding: no algorithm on every promised integer matrix input → no total computable Boolean function on the four signed integer entries, correct on every promised matrix; reason: the entry tuple is an effective bijective matrix encoding and correctness outside the promise is unrestricted
--   - encoding: finite sets of exactly 5799 distinct matrices → injective lists of exactly 5799 row-major four-entry encodings; reason: finite sets and these lists have computably equivalent presentations; every list order is included
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Corollary 1.2, PDF p. 3 / printed p. 1

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem exact_fixed_image_mortality_undecidable
    : (∃ (p : ℕ) (G : Finset ZMat) (L : Submodule ℚ QVec),
        Nat.Prime p ∧ G.card = 5798 ∧ DeterminantsAtPrime G p ∧
        IsRationalLine L ∧ NoPromisedDecider G L) ∧ NoExactSizeDecider 5799 := by sorry

end IntegerMatrixMortality.FixedImage
