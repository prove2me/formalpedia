-- Prove2me | Theorems.Thm_GlobalTheory_CompleteJoin_exists_normal_subring
-- name    : GlobalTheory.CompleteJoin.exists_normal_subring
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:51:09.973482+00:00
-- url     : https://prove2.me/theorems/0f37c588-6334-4ffb-975f-5d7e9f10f698
-- title:
--   Complete Join: exists normal subring
-- statement:
--   The Complete Join construction uses the exists normal subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsCompleteNormalSubringJoin.lean#L118-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsCompleteNormalSubringJoin.lean#L118-L132

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralClosureFiniteLocalCompleteMixedCharStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCompleteNormalSubringJoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open GlobalTheory.CompleteJoin
variable {C : Type} [NormedField C] [IsUltrametricDist C]
omit [IsUltrametricDist C]

theorem GlobalTheory.CompleteJoin.exists_normal_subring (S : Subring C)
    (h : Module.Finite S (integralClosure S (FractionRing S))) :
    ∃ (S' : Subring C) (ψ : S →+* S'), ψ.Finite ∧ (∀ a, (ψ a : C) = a) ∧ IsIntegrallyClosed S' := by sorry
