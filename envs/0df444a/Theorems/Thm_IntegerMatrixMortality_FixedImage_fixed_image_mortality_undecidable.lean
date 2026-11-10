-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_fixed_image_mortality_undecidable
-- name    : IntegerMatrixMortality.FixedImage.fixed_image_mortality_undecidable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:30.386443+00:00
-- url     : https://prove2.me/theorems/08840c4b-5faa-4aa2-96e3-d559035d20d9
-- title:
--   Theorem 1.1 — Mortality with one variable matrix
-- statement:
--   There exist a prime p, a fixed finite set G of nonsingular integer two-by-two matrices with determinants in {p,−p}, and a fixed rational line L such that no total computable function of the four signed entries decides
--
--   $$\operatorname{Mortal}(G\cup\{R\})$$
--
--   for every nonzero rank-one integer matrix R with rational image L. The prime, family and line are chosen before all proposed algorithms and all promised inputs. The promise covers every such R, not just a selected reduction sequence.
--
--   Differences from the source:
--   - encoding: no algorithm on every promised integer matrix input → no total computable Boolean function on the four signed integer entries, correct on every promised matrix; reason: the entry tuple is an effective bijective matrix encoding and correctness outside the promise is unrestricted
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Theorem 1.1, PDF p. 3 / printed p. 1

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem fixed_image_mortality_undecidable
    : ∃ (p : ℕ) (G : Finset ZMat) (L : Submodule ℚ QVec),
      Nat.Prime p ∧ DeterminantsAtPrime G p ∧ IsRationalLine L ∧ NoPromisedDecider G L := by sorry

end IntegerMatrixMortality.FixedImage
