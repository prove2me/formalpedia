-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_auxiliary_maps_preserve_validity
-- name    : IntegerMatrixMortality.FixedImage.auxiliary_maps_preserve_validity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:13.106484+00:00
-- url     : https://prove2.me/theorems/e5d70694-22d5-4dea-8e9a-aae6a89d5dd1
-- title:
--   Lemma 5.3 — Auxiliary maps preserve valid and error points
-- statement:
--   Let p≥7 be prime, c,h∈ℤ and δ∈{−1,1}. Integer translation z↦z+c and Mδ,h(z)=δz/(1+phz) each map V bijectively to V and E bijectively to E. For every residue representative e of z∈V,
--
--   $$M_{\delta,h}(z)\equiv\delta e\pmod p.$$
--
--   Both bijections are on the full projective line, so poles and infinity are included. These auxiliary operations cannot erase an error.
--
--   Differences from the source:
--   - encoding: rational projective points, residues and matrix words → Option ℚ with explicit poles, reduced-denominator congruence and reversed list products; reason: infinity and empty words have their source values
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Lemma 5.3, PDF p. 10 / printed p. 8

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem auxiliary_maps_preserve_validity
    (p : ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p) (c h : ℤ) (neg : Bool) :
      Set.BijOn (translate c) {z | Valid p z} {z | Valid p z} ∧
      Set.BijOn (translate c) {z | Error p z} {z | Error p z} ∧
      Set.BijOn (auxiliary p neg h) {z | Valid p z} {z | Valid p z} ∧
      Set.BijOn (auxiliary p neg h) {z | Error p z} {z | Error p z} ∧
      ∀ z e, HasResidue p z e →
        HasResidue p (auxiliary p neg h z) ((if neg then -1 else 1) * e) := by sorry

end IntegerMatrixMortality.FixedImage
