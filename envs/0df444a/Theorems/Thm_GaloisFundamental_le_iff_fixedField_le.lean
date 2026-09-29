-- Prove2me | Theorems.Thm_GaloisFundamental_le_iff_fixedField_le
-- name    : GaloisFundamental.le_iff_fixedField_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:03:44.822548+00:00
-- url     : https://prove2.me/theorems/a13d86dd-f39c-4f53-b7ab-26a8ef741ad1
-- title:
--   The Galois correspondence is inclusion-reversing
-- statement:
--   Let $E/F$ be a finite Galois extension with Galois group $G$. For subgroups $H_1, H_2 \le G$,
--
--   $$H_1 \subseteq H_2 \iff E^{H_1} \supseteq E^{H_2}.$$
-- source:
--   Wikipedia, "Fundamental theorem of Galois theory", revision oldid=1345286594, https://en.wikipedia.org/w/index.php?title=Fundamental_theorem_of_Galois_theory&oldid=1345286594, section "Properties of the correspondence", first bullet ("It is inclusion-reversing")

import Mathlib

namespace GaloisFundamental

theorem le_iff_fixedField_le (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (H₁ H₂ : Subgroup (E ≃ₐ[F] E)) :
    H₁ ≤ H₂ ↔ IntermediateField.fixedField H₂ ≤ IntermediateField.fixedField H₁ := by sorry

end GaloisFundamental
