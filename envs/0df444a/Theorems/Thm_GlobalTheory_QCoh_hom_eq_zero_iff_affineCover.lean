-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_hom_eq_zero_iff_affineCover
-- name    : GlobalTheory.QCoh.hom_eq_zero_iff_affineCover
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:26.335837+00:00
-- url     : https://prove2.me/theorems/d9b1527a-1c35-5043-9be8-dbbfebcd2a27
-- title:
--   QCoh: hom eq zero iff affine Cover
-- statement:
--   The QCoh construction uses the hom eq zero iff affine Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L653-L659
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L653-L659

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

theorem GlobalTheory.QCoh.hom_eq_zero_iff_affineCover {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰)
    (haff : ∀ i, IsAffineOpen (𝒰 i)) [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    φ = 0 ↔ ∀ i s, φ.app (𝒰 i) s = 0 := by sorry
