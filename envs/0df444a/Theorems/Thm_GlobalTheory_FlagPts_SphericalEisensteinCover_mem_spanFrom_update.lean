-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_mem_spanFrom_update
-- name    : GlobalTheory.FlagPts.SphericalEisensteinCover.mem_spanFrom_update
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:45.064251+00:00
-- url     : https://prove2.me/theorems/f3f58481-3da2-4148-b1c2-bac4aeb259bd
-- title:
--   Spherical Eisenstein Cover: mem span From update
-- statement:
--   The Spherical Eisenstein Cover construction uses the mem span From update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L87-L90

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
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]

theorem GlobalTheory.FlagPts.SphericalEisensteinCover.mem_spanFrom_update (f : ℕ → W) (N m : ℕ) (v : W) (h : m < N) :
    v ∈ spanFrom k (Function.update f m v) N m := by sorry
