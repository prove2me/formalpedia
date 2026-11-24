-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_InvMap_inv_and_Delta_map
-- name    : GlobalTheory.JR.Step.InvMap.inv_and_Delta_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:36:01.01577+00:00
-- url     : https://prove2.me/theorems/6bd7ea9d-6760-4982-a525-b0254f6dc435
-- title:
--   Inv Map: inv and Delta map
-- statement:
--   The Inv Map construction uses the inv and Delta map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedInvariantsAndHankelDetMapRingHom.lean#L62-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedInvariantsAndHankelDetMapRingHom.lean#L62-L76

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
open Matrix MeasureTheory Filter Topology
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ}

theorem GlobalTheory.JR.Step.InvMap.inv_and_Delta_map : ∀ (k k' : Type) [CommRing k] [CommRing k'] (φ : k →+* k') (r : ℕ),
    (∀ Y : _root_.GlobalTheory.JR.Gl r k, _root_.GlobalTheory.JR.inv (_root_.GlobalTheory.JR.Step.glMap φ Y) = (_root_.GlobalTheory.JR.inv Y).map φ) ∧
      (∀ a : _root_.GlobalTheory.JR.Inv r k, _root_.GlobalTheory.JR.Delta (a.map φ) = φ (_root_.GlobalTheory.JR.Delta a)) := by sorry
