-- Prove2me | Theorems.Thm_GlobalTheory_CompleteJoin_padicInt_ringHom_ext
-- name    : GlobalTheory.CompleteJoin.padicInt_ringHom_ext
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:51:09.367876+00:00
-- url     : https://prove2.me/theorems/07049a7d-b620-4536-a02b-dfb8213fd74f
-- title:
--   Complete Join: padic Int ring Hom ext
-- statement:
--   The Complete Join construction uses the padic Int ring Hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsCompleteNormalSubringJoin.lean#L29-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsCompleteNormalSubringJoin.lean#L29-L44

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

theorem GlobalTheory.CompleteJoin.padicInt_ringHom_ext {p : ℕ} [Fact p.Prime] (hp : ‖(p : C)‖ < 1) (a b : ℤ_[p] →+* C)
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ x, ‖b x‖ ≤ 1) : a = b := by sorry
