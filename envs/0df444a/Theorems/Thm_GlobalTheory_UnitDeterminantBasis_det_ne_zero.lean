-- Prove2me | Theorems.Thm_GlobalTheory_UnitDeterminantBasis_det_ne_zero
-- name    : GlobalTheory.UnitDeterminantBasis.det_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:31:12.422456+00:00
-- url     : https://prove2.me/theorems/3c7f5d9b-a436-499d-9465-acab66c99d43
-- title:
--   Unit Determinant Basis: det ne zero
-- statement:
--   The Unit Determinant Basis construction uses the det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitDeterminantBasis.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitDeterminantBasis.lean#L9-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitDeterminantBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.UnitDeterminantBasis

theorem GlobalTheory.UnitDeterminantBasis.det_ne_zero {k A O : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing O]
    [Algebra k O] [IsDomain O] {n : ℕ} {e : A}
    (b : Module.Basis (Fin n) k (LinearMap.range (LinearMap.mulLeft k e)))
    (T : Fin n → (A →ₐ[k] O)) (hT : Function.Injective T) (hTe : ∀ j, T j e = 1) :
    (Matrix.of fun i j => T j (b i : A)).det ≠ 0 := by sorry
