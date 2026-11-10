-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_digit_deletion_detects_errors
-- name    : IntegerMatrixMortality.FixedImage.digit_deletion_detects_errors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:02.795949+00:00
-- url     : https://prove2.me/theorems/f1c9b1fa-0b03-4117-ae0b-e59e2dbf0257
-- title:
--   Lemma 5.2 — Digit deletion detects errors
-- statement:
--   Let p≥7 be prime, V the rational points with denominator prime to p, E its complement in the rational projective line, and e an arbitrary integer. The digit-deletion map Dₑ sends E into E. For every z∈V,
--
--   $$D_e(z)\in V\iff z\equiv e\pmod p.$$
--
--   This detects a failed digit choice, including on projective infinity, and supports rejection invariance.
--
--   Differences from the source:
--   - encoding: rational projective points, residues and matrix words → Option ℚ with explicit poles, reduced-denominator congruence and reversed list products; reason: infinity and empty words have their source values
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Lemma 5.2, PDF p. 9 / printed p. 7

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem digit_deletion_detects_errors
    (p : ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p) (e : ℤ) :
      (∀ z, Error p z → Error p (deleteDigit p e z)) ∧
      (∀ z, Valid p z → (Valid p (deleteDigit p e z) ↔ HasResidue p z e)) := by sorry

end IntegerMatrixMortality.FixedImage
