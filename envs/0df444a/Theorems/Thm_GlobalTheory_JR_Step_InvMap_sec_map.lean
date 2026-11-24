-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_InvMap_sec_map
-- name    : GlobalTheory.JR.Step.InvMap.sec_map
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:46.485924+00:00
-- url     : https://prove2.me/theorems/9e5f81c3-4726-468e-8851-9ccca80f40f5
-- title:
--   Inv Map: sec map
-- statement:
--   The Inv Map construction uses the sec map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedInvariantsAndHankelDetMapRingHom.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedInvariantsAndHankelDetMapRingHom.lean#L24-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.InvMap
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ}

theorem GlobalTheory.JR.Step.InvMap.sec_map (a : Inv r k) : sec (a.map φ) = glMap φ (sec a) := by sorry
