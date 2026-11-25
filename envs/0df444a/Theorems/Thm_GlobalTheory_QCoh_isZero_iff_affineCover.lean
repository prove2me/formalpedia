-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isZero_iff_affineCover
-- name    : GlobalTheory.QCoh.isZero_iff_affineCover
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:11:24.190333+00:00
-- url     : https://prove2.me/theorems/a704aaee-ac32-41e8-b85c-3dc1b0c72a4d
-- title:
--   QCoh: is Zero iff affine Cover
-- statement:
--   The QCoh construction uses the is Zero iff affine Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L365-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L365-L380

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

theorem GlobalTheory.QCoh.isZero_iff_affineCover [M.IsQuasicoherent] :
    IsZero M ↔ ∀ i, Subsingleton Γ(M, 𝒰 i) := by sorry
