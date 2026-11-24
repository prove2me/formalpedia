-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_finrank_sup_span
-- name    : GlobalTheory.FlagPts.SphericalEisensteinCover.finrank_sup_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:54:51.497091+00:00
-- url     : https://prove2.me/theorems/4decabe7-05db-453d-88ff-7ae516c136d9
-- title:
--   Spherical Eisenstein Cover: finrank sup span
-- statement:
--   The Spherical Eisenstein Cover construction uses the finrank sup span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L44-L50

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

theorem GlobalTheory.FlagPts.SphericalEisensteinCover.finrank_sup_span [FiniteDimensional k W] (G : Submodule k W) (v : W) (hv : v ∉ G) :
    finrank k (G ⊔ k ∙ v : Submodule k W) = finrank k G + 1 := by sorry
