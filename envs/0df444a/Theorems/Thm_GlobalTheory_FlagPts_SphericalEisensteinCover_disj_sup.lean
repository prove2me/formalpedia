-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_disj_sup
-- name    : GlobalTheory.FlagPts.SphericalEisensteinCover.disj_sup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:03.373564+00:00
-- url     : https://prove2.me/theorems/96cd602c-9eac-449a-95d6-9639d85fe129
-- title:
--   Spherical Eisenstein Cover: disj sup
-- statement:
--   The Spherical Eisenstein Cover construction uses the disj sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L25-L42

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

theorem GlobalTheory.FlagPts.SphericalEisensteinCover.disj_sup (P G : Submodule k W) (v : W) (hPG : Disjoint P G) (hv : v ∉ P ⊔ G) :
    Disjoint P (G ⊔ k ∙ v) := by sorry
