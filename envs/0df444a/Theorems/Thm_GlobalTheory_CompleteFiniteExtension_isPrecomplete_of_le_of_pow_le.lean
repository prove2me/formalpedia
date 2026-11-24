-- Prove2me | Theorems.Thm_GlobalTheory_CompleteFiniteExtension_isPrecomplete_of_le_of_pow_le
-- name    : GlobalTheory.CompleteFiniteExtension.isPrecomplete_of_le_of_pow_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:57.880806+00:00
-- url     : https://prove2.me/theorems/fd77a42b-48d7-4eb7-ba71-1360c67f9fe5
-- title:
--   Complete Finite Extension: is Precomplete of le of pow le
-- statement:
--   The Complete Finite Extension construction uses the is Precomplete of le of pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompleteDvrFiniteSubalgebra.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompleteDvrFiniteSubalgebra.lean#L15-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPrecompleteOfLeOfPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Theorems.Thm_GlobalTheory_PrecompleteOfPowLe_isPrecomplete_of_le_of_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.CompleteFiniteExtension
open IsLocalRing

theorem GlobalTheory.CompleteFiniteExtension.isPrecomplete_of_le_of_pow_le {A : Type*} [CommRing A] {I J : Ideal A} (hJ : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [IsPrecomplete J A] : IsPrecomplete I A := by sorry
