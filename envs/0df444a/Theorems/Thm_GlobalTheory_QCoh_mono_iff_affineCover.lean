-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_mono_iff_affineCover
-- name    : GlobalTheory.QCoh.mono_iff_affineCover
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:15:59.426474+00:00
-- url     : https://prove2.me/theorems/4be81d3a-310e-574b-98c0-9caf0b64b952
-- title:
--   QCoh: mono iff affine Cover
-- statement:
--   The QCoh construction uses the mono iff affine Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L384-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L384-L389

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}
variable {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i))
include hcov haff
variable [M.IsQuasicoherent] [N.IsQuasicoherent]

theorem GlobalTheory.QCoh.mono_iff_affineCover (φ : M ⟶ N) : Mono φ ↔ ∀ i, Function.Injective (φ.app (𝒰 i)) := by sorry
