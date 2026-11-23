-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_InvMap_mom_glMap
-- name    : GlobalTheory.JR.Step.InvMap.mom_glMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:33.41525+00:00
-- url     : https://prove2.me/theorems/0d4c7668-981a-46c8-b697-1b4ae1843bc7
-- title:
--   Inv Map: mom gl Map
-- statement:
--   The Inv Map construction uses the mom gl Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedInvariantsAndHankelDetMapRingHom.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedInvariantsAndHankelDetMapRingHom.lean#L11-L15

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

theorem GlobalTheory.JR.Step.InvMap.mom_glMap (Y : Gl r k) (i : ℕ) : mom (glMap φ Y) i = φ (mom Y i) := by sorry
