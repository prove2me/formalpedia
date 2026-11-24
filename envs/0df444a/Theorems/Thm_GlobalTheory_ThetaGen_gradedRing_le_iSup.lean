-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGen_gradedRing_le_iSup
-- name    : GlobalTheory.ThetaGen.gradedRing_le_iSup
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:06:15.401394+00:00
-- url     : https://prove2.me/theorems/b4301178-d69b-49c7-ad7b-0d27f41b4330
-- title:
--   Theta Gen: graded Ring le i Sup
-- statement:
--   The Theta Gen construction uses the graded Ring le i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsHomogeneousOfMemSpanPow.lean#L66-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsHomogeneousOfMemSpanPow.lean#L66-L84

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {X : Type}
variable (R : ℕ → Submodule ℂ (X → ℂ))

theorem GlobalTheory.ThetaGen.gradedRing_le_iSup (h1 : (1 : X → ℂ) ∈ R 0)
    (hmul : ∀ a b, R a * R b ≤ R (a + b)) {F : ℂ × X → ℂ} (hF : F ∈ gradedRing R) :
    F ∈ Submodule.span ℂ {F | ∃ d, ∃ f ∈ R d, F = homog d f} := by sorry
