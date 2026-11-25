-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isZero_iff_forall_affine
-- name    : GlobalTheory.QCoh.isZero_iff_forall_affine
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:45.162145+00:00
-- url     : https://prove2.me/theorems/0618d0e5-d34b-5a98-b90c-d114717a6377
-- title:
--   QCoh: is Zero iff forall affine
-- statement:
--   The QCoh construction uses the is Zero iff forall affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L628-L631
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L628-L631

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
variable [M.IsQuasicoherent] [N.IsQuasicoherent]

theorem GlobalTheory.QCoh.isZero_iff_forall_affine :
    IsZero M ↔ ∀ U, IsAffineOpen U → Subsingleton Γ(M, U) := by sorry
