-- Prove2me | Theorems.Thm_GaloisFundamental_finrank_fixedField
-- name    : GaloisFundamental.finrank_fixedField
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:06:23.833986+00:00
-- url     : https://prove2.me/theorems/9a4bd19d-64a3-4ff6-a9ba-5c40c9d7295a
-- title:
--   Degrees in the Galois correspondence: $[E:E^H] = |H|$ and $[E^H:F] = [G:H]$
-- statement:
--   Let $E/F$ be a finite Galois extension with Galois group $G$, and let $H \le G$ be a subgroup. Then
--
--   $$[E : E^H] = |H| \qquad\text{and}\qquad [E^H : F] = [G : H].$$
-- source:
--   Wikipedia, "Fundamental theorem of Galois theory", revision oldid=1345286594, https://en.wikipedia.org/w/index.php?title=Fundamental_theorem_of_Galois_theory&oldid=1345286594, section "Properties of the correspondence", second bullet ("if H is a subgroup of Gal(E/F), then |H| = [E:E^H] and |Gal(E/F)/H| = [E^H:F]")

import Mathlib

namespace GaloisFundamental

theorem finrank_fixedField (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (H : Subgroup (E ≃ₐ[F] E)) :
    Module.finrank (IntermediateField.fixedField H) E = Nat.card H ∧
      Module.finrank F (IntermediateField.fixedField H) = H.index := by sorry

end GaloisFundamental
