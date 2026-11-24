-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_not_le_of_finrank
-- name    : GlobalTheory.FlagPts.SphericalEisensteinCover.not_le_of_finrank
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:06.749546+00:00
-- url     : https://prove2.me/theorems/50c3ec54-5f79-456e-a7e7-a5c45f12f7cd
-- title:
--   Spherical Eisenstein Cover: not le of finrank
-- statement:
--   The Spherical Eisenstein Cover construction uses the not le of finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L52-L54

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

theorem GlobalTheory.FlagPts.SphericalEisensteinCover.not_le_of_finrank [FiniteDimensional k W] (B H G : Submodule k W) (hGB : ¬ G ≤ B) (hGH : G ≤ H)
    (hd : finrank k H ≤ finrank k B) : ¬ B ≤ H := by sorry
