-- Prove2me | Theorems.Thm_InverseGalois_fixedPoints_fieldRange_isRealizable
-- name    : InverseGalois.fixedPoints_fieldRange_isRealizable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T01:35:08.179931+00:00
-- url     : https://prove2.me/theorems/83746b73-c472-46b7-b037-5fa6c15a366f
-- title:
--   A complex copy of a fixed field realizes the acting group
-- statement:
--   Let a finite group $G$ act faithfully by field automorphisms on a characteristic-zero field $L$. Let $F=L^G$ be its fixed field, and let $φ:F→ℂ$ be a rational algebra homomorphism. Then the image field $φ(F)$ realizes $G$ as a Galois group:
--
--   $$
--   G ≅ Gal(L/φ(F)).
--   $$
--
--   The scalar structure on $L$ is transported across the isomorphism $F≅φ(F)$. This packages fixed-field realization together with change of the base field along an embedding.
-- source:
--   Mathlib, fixed fields of faithful finite group actions, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Galois/IsGaloisGroup.lean#L189-L214; field-range equivalence, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IntermediateField/Basic.lean#L535-L552

import Definitions.Def_InverseGalois_realizability
import Mathlib

namespace InverseGalois

universe u

theorem fixedPoints_fieldRange_isRealizable (G : Type u) (L : Type)
    [Fintype G] [Group G]
    [Field L] [CharZero L] [MulSemiringAction G L] [FaithfulSMul G L]
    (φ : FixedPoints.subfield G L →ₐ[ℚ] ℂ) :
    IsRealizable φ.fieldRange G := by sorry
