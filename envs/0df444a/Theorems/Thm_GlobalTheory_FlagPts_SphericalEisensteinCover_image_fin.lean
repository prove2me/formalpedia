-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_image_fin
-- name    : GlobalTheory.FlagPts.SphericalEisensteinCover.image_fin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:17.500335+00:00
-- url     : https://prove2.me/theorems/6e52d101-eade-4a4b-baa6-ecb5572e0042
-- title:
--   Spherical Eisenstein Cover: image fin
-- statement:
--   The Spherical Eisenstein Cover construction uses the image fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean#L92-L99

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

theorem GlobalTheory.FlagPts.SphericalEisensteinCover.image_fin (f : ℕ → W) (N m : ℕ) :
    (fun i : Fin N => f i) '' {a : Fin N | m ≤ (a : ℕ)} = f '' {a | m ≤ a ∧ a < N} := by sorry
