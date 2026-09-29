-- Prove2me | Theorems.Thm_GaloisFundamental_isGalois_iff_galois_correspondence
-- name    : GaloisFundamental.isGalois_iff_galois_correspondence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T22:55:29.055682+00:00
-- url     : https://prove2.me/theorems/bb5dd5a3-1680-49c0-a847-a79e07e76bee
-- title:
--   Fundamental theorem of Galois theory: $E/F$ is Galois iff the correspondence is one-to-one
-- statement:
--   Let $E/F$ be a finite field extension, and let $G = \operatorname{Aut}(E/F)$ be its group of $F$-automorphisms. For an intermediate field $K$ write $\operatorname{Aut}(E/K) \le G$ for the automorphisms fixing $K$ pointwise, and for a subgroup $H \le G$ write $E^H$ for the fixed field of $H$. Then $E/F$ is Galois (normal and separable) **if and only if** the maps $K \mapsto \operatorname{Aut}(E/K)$ and $H \mapsto E^H$ are mutually inverse, i.e.
--
--   $$E^{\operatorname{Aut}(E/K)} = K \quad\text{for every intermediate field } K, \qquad \operatorname{Aut}(E/E^H) = H \quad\text{for every subgroup } H \le G.$$
-- source:
--   Wikipedia, "Fundamental theorem of Galois theory", revision oldid=1345286594, https://en.wikipedia.org/w/index.php?title=Fundamental_theorem_of_Galois_theory&oldid=1345286594, lead section and section "Explicit description of the correspondence" ("this correspondence is a one-to-one correspondence if (and only if) E/F is a Galois extension")

import Mathlib

namespace GaloisFundamental

theorem isGalois_iff_galois_correspondence (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    IsGalois F E ↔
      ((∀ K : IntermediateField F E, IntermediateField.fixedField K.fixingSubgroup = K) ∧
        ∀ H : Subgroup (E ≃ₐ[F] E), (IntermediateField.fixedField H).fixingSubgroup = H) := by sorry

end GaloisFundamental
