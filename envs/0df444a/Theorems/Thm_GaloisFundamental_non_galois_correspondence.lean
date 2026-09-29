-- Prove2me | Theorems.Thm_GaloisFundamental_non_galois_correspondence
-- name    : GaloisFundamental.non_galois_correspondence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T23:46:01.177244+00:00
-- url     : https://prove2.me/theorems/822eba9d-cdad-4e82-81a5-073af5a1a57e
-- title:
--   Galois correspondence for a finite non-Galois extension
-- statement:
--   Let $E/F$ be a finite field extension that is **not** Galois, and let $G = \operatorname{Aut}(E/F)$. Then:
--
--   - the map $H \mapsto E^H$ from subgroups of $G$ to intermediate fields is injective but not surjective;
--   - the map $K \mapsto \operatorname{Aut}(E/K)$ from intermediate fields to subgroups of $G$ is surjective but not injective;
--   - $F$ is not the fixed field of any subgroup of $G$: $E^H \ne F$ for every $H \le G$.
-- source:
--   Wikipedia, "Fundamental theorem of Galois theory", revision oldid=1345286594, https://en.wikipedia.org/w/index.php?title=Fundamental_theorem_of_Galois_theory&oldid=1345286594, section "Explicit description of the correspondence", last paragraph ("If E/F is not Galois, then the correspondence gives only an injective (but not surjective) map ... In particular, if E/F is not Galois, then F is not the fixed field of any subgroup")

import Mathlib

namespace GaloisFundamental

theorem non_galois_correspondence (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (hE : ¬ IsGalois F E) :
    Function.Injective (fun H : Subgroup (E ≃ₐ[F] E) => IntermediateField.fixedField H) ∧
      ¬ Function.Surjective (fun H : Subgroup (E ≃ₐ[F] E) => IntermediateField.fixedField H) ∧
      Function.Surjective (fun K : IntermediateField F E => K.fixingSubgroup) ∧
      ¬ Function.Injective (fun K : IntermediateField F E => K.fixingSubgroup) ∧
      ∀ H : Subgroup (E ≃ₐ[F] E), IntermediateField.fixedField H ≠ ⊥ := by sorry

end GaloisFundamental
