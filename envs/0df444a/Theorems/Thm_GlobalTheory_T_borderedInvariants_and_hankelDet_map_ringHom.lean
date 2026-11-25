-- Prove2me | Theorems.Thm_GlobalTheory_T_borderedInvariants_and_hankelDet_map_ringHom
-- name    : GlobalTheory.T.borderedInvariants_and_hankelDet_map_ringHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:43.443774+00:00
-- url     : https://prove2.me/theorems/19c2c988-f589-44e6-a93b-8ef86ffce841
-- title:
--   T: bordered Invariants and hankel Det map ring Hom
-- statement:
--   The T construction uses the bordered Invariants and hankel Det map ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedInvariantsAndHankelDetMapRingHomStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedInvariantsAndHankelDetMapRingHomStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHomStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.borderedInvariants_and_hankelDet_map_ringHom : ∀ (k k' : Type) [CommRing k] [CommRing k'] (φ : k →+* k') (r : ℕ), (∀ Y : Gl r k, inv (GlobalTheory.JR.Step.glMap φ Y) = (inv Y).map φ) ∧ (∀ a : Inv r k, Delta (a.map φ) = φ (Delta a)) := by sorry
