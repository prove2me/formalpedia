-- Prove2me | Theorems.Thm_GlobalTheory_exists_complete_dvr_finite_subalgebra
-- name    : GlobalTheory.exists_complete_dvr_finite_subalgebra
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:20.32604+00:00
-- url     : https://prove2.me/theorems/edf95f40-6619-4ddf-b19a-3a4ccbc3066e
-- title:
--   Global Theory: exists complete dvr finite subalgebra
-- statement:
--   The Global Theory construction uses the exists complete dvr finite subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompleteDvrFiniteSubalgebra.lean#L42-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompleteDvrFiniteSubalgebra.lean#L42-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPrecompleteOfLeOfPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_complete_dvr_finite_subalgebra :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] (F : Type) [Field F]
      [Algebra V F] [FaithfulSMul V F] [Algebra.IsAlgebraic V F] (s : Finset F),
      ∃ (W : Subalgebra V F) (_ : IsDiscreteValuationRing W),
        IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
        IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧
        Module.Finite V W ∧ Module.Free V W ∧ IsLocalHom (algebraMap V W) ∧
        (∀ x ∈ s, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) ∧
        ∀ x ∈ s, IsIntegral V x → x ∈ W := by sorry
