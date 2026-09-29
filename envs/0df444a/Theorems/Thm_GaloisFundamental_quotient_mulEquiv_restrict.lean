-- Prove2me | Theorems.Thm_GaloisFundamental_quotient_mulEquiv_restrict
-- name    : GaloisFundamental.quotient_mulEquiv_restrict
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:31:19.094338+00:00
-- url     : https://prove2.me/theorems/c67c7bb0-b798-45a7-bd09-cc9b787f786c
-- title:
--   Restriction induces $\operatorname{Gal}(E/F)/H \cong \operatorname{Gal}(E^H/F)$ for normal $H$
-- statement:
--   Let $E/F$ be a finite Galois extension with Galois group $G$, and let $H$ be a normal subgroup of $G$ (so that $E^H/F$ is normal). Then restriction of automorphisms to $E^H$ induces a group isomorphism
--
--   $$\varphi : G/H \xrightarrow{\ \sim\ } \operatorname{Gal}(E^H/F), \qquad \varphi(\sigma H) = \sigma|_{E^H}.$$
--
--   (The normality of $E^H/F$ is included as a hypothesis so that the restriction map can be written down; it is equivalent to the normality of $H$.)
-- source:
--   Wikipedia, "Fundamental theorem of Galois theory", revision oldid=1345286594, https://en.wikipedia.org/w/index.php?title=Fundamental_theorem_of_Galois_theory&oldid=1345286594, section "Properties of the correspondence", third bullet ("In this case, the restriction of the elements of Gal(E/F) to E^H induces an isomorphism between Gal(E^H/F) and the quotient group Gal(E/F)/H")

import Mathlib

namespace GaloisFundamental

theorem quotient_mulEquiv_restrict (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (H : Subgroup (E ≃ₐ[F] E)) [H.Normal]
    [Normal F (IntermediateField.fixedField H)] :
    ∃ φ : ((E ≃ₐ[F] E) ⧸ H) ≃*
        (IntermediateField.fixedField H ≃ₐ[F] IntermediateField.fixedField H),
      ∀ σ : E ≃ₐ[F] E,
        φ (QuotientGroup.mk σ) = AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) σ := by
  sorry

end GaloisFundamental
