-- Prove2me | Theorems.Thm_GlobalTheory_ConeImage_exists_compact_cover
-- name    : GlobalTheory.ConeImage.exists_compact_cover
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:25:34.465808+00:00
-- url     : https://prove2.me/theorems/c79c0853-b531-434e-aec9-704065a37f88
-- title:
--   Cone Image: exists compact cover
-- statement:
--   The Cone Image construction uses the exists compact cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L12-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L12-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange
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
open GlobalTheory GlobalTheory.ConeImage

theorem GlobalTheory.ConeImage.exists_compact_cover {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (h : Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤) :
    ∃ K : Set (Fin g → ℂ), IsCompact K ∧ ∀ z, ∃ w ∈ K, ∃ n n' : Fin g → ℤ,
      z = w + τ *ᵥ ofIntVec n + ofIntVec n' := by sorry
