-- Prove2me | Theorems.Thm_GlobalTheory_CompleteJoin_subring_of_finite
-- name    : GlobalTheory.CompleteJoin.subring_of_finite
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:50:38.628811+00:00
-- url     : https://prove2.me/theorems/30fad50a-26f7-4adc-998f-4d969cebf564
-- title:
--   Complete Join: subring of finite
-- statement:
--   The Complete Join construction uses the subring of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsCompleteNormalSubringJoin.lean#L46-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsCompleteNormalSubringJoin.lean#L46-L86

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

theorem GlobalTheory.CompleteJoin.subring_of_finite {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Subring C) (φ : R →+* S) (hφ : φ.Finite)
    (h1 : ∀ a, ‖(φ a : C)‖ ≤ 1) (h2 : ∀ a ∈ maximalIdeal R, ‖(φ a : C)‖ < 1) :
    ∃ _ : IsLocalRing S, IsNoetherianRing S ∧ IsAdicComplete (maximalIdeal S) S ∧
      (∀ z : S, ‖(z : C)‖ ≤ 1) ∧ ∀ z : S, z ∈ maximalIdeal S ↔ ‖(z : C)‖ < 1 := by sorry
