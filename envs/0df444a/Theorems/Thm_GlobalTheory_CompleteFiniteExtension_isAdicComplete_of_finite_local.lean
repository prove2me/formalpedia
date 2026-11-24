-- Prove2me | Theorems.Thm_GlobalTheory_CompleteFiniteExtension_isAdicComplete_of_finite_local
-- name    : GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:35.577217+00:00
-- url     : https://prove2.me/theorems/d72d28bd-6158-4797-a502-f98aa67fe9f6
-- title:
--   Complete Finite Extension: is Adic Complete of finite local
-- statement:
--   The Complete Finite Extension construction uses the is Adic Complete of finite local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompleteDvrFiniteSubalgebra.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompleteDvrFiniteSubalgebra.lean#L26-L38

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
open GlobalTheory.CompleteFiniteExtension
open IsLocalRing

theorem GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local (R S : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : IsAdicComplete (maximalIdeal S) S := by sorry
