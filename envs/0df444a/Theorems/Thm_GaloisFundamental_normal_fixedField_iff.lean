-- Prove2me | Theorems.Thm_GaloisFundamental_normal_fixedField_iff
-- name    : GaloisFundamental.normal_fixedField_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:07:38.132263+00:00
-- url     : https://prove2.me/theorems/3c6ded9f-1635-4b5d-926b-aa37696f258a
-- title:
--   $E^H/F$ is normal iff $H$ is a normal subgroup
-- statement:
--   Let $E/F$ be a finite Galois extension with Galois group $G$, and let $H \le G$. Then the fixed field $E^H$ is a normal extension of $F$ if and only if $H$ is a normal subgroup of $G$.
-- source:
--   Wikipedia, "Fundamental theorem of Galois theory", revision oldid=1345286594, https://en.wikipedia.org/w/index.php?title=Fundamental_theorem_of_Galois_theory&oldid=1345286594, section "Properties of the correspondence", third bullet ("The field E^H is a normal extension of F ... if and only if H is a normal subgroup of Gal(E/F)")

import Mathlib

namespace GaloisFundamental

theorem normal_fixedField_iff (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (H : Subgroup (E ≃ₐ[F] E)) :
    Normal F (IntermediateField.fixedField H) ↔ H.Normal := by sorry

end GaloisFundamental
