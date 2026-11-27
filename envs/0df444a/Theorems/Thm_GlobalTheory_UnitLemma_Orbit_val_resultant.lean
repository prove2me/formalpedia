-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_val_resultant
-- name    : GlobalTheory.UnitLemma.Orbit.val_resultant
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:28.220852+00:00
-- url     : https://prove2.me/theorems/151d036c-dddb-4869-ac24-62a834cf1e00
-- title:
--   Orbit: val resultant
-- statement:
--   The Orbit construction uses the val resultant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L103-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L103-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}

theorem GlobalTheory.UnitLemma.Orbit.val_resultant (B C : InvAlg K) (hB : B.P.Separable) (hC : C.P.Separable) (iB : IsIntegral K.O B.g)
    (iC : IsIntegral K.O C.g) (f : K.O[X]) (h0 : aeval B.g f = 0) (h1 : aeval C.g f = 1) :
    val K.O (resultant B.P C.P) = 0 := by sorry
