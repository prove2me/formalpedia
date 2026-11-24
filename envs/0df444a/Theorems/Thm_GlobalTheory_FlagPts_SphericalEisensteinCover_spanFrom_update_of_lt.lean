-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_spanFrom_update_of_lt
-- name    : GlobalTheory.FlagPts.SphericalEisensteinCover.spanFrom_update_of_lt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:56:32.894999+00:00
-- url     : https://prove2.me/theorems/52756588-0490-4749-ba46-7e2c322e8b48
-- title:
--   Spherical Eisenstein Cover: span From update of lt
-- statement:
--   The Spherical Eisenstein Cover construction uses the span From update of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L60-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]

theorem GlobalTheory.FlagPts.SphericalEisensteinCover.spanFrom_update_of_lt (f : ℕ → W) (N m m' : ℕ) (v : W) (h : m < m') :
    spanFrom k (Function.update f m v) N m' = spanFrom k f N m' := by sorry
