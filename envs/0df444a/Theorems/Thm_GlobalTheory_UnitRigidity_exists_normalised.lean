-- Prove2me | Theorems.Thm_GlobalTheory_UnitRigidity_exists_normalised
-- name    : GlobalTheory.UnitRigidity.exists_normalised
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:19:34.155309+00:00
-- url     : https://prove2.me/theorems/3613b21a-d3cc-4d29-8a5c-70102692c90c
-- title:
--   Unit Rigidity: exists normalised
-- statement:
--   The Unit Rigidity construction uses the exists normalised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L13-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L13-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.UnitRigidity

theorem GlobalTheory.UnitRigidity.exists_normalised {K L B ι : Type*} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    (b : Module.Basis ι K B) (O : ValuationSubring L) [Algebra K O] [IsScalarTower K O L]
    (w : L ⊗[K] B) (hw : w ≠ 0) :
    ∃ (a : L) (w' : O ⊗[K] B), a ≠ 0 ∧
      w = a • Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O L) (AlgHom.id K B) w' ∧
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O (IsLocalRing.ResidueField O))
        (AlgHom.id K B) w' ≠ 0 ∧
      ∀ i, ∃ c : O, (Algebra.TensorProduct.basis L b).repr w i = a * c := by sorry
