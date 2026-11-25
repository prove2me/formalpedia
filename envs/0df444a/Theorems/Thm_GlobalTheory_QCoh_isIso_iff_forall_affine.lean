-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isIso_iff_forall_affine
-- name    : GlobalTheory.QCoh.isIso_iff_forall_affine
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:51.110367+00:00
-- url     : https://prove2.me/theorems/ef80c19c-43c7-5b5c-8ab6-5417ec4e0e9a
-- title:
--   QCoh: is Iso iff forall affine
-- statement:
--   The QCoh construction uses the is Iso iff forall affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L638-L641
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L638-L641

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

theorem GlobalTheory.QCoh.isIso_iff_forall_affine (φ : M ⟶ N) :
    IsIso φ ↔ ∀ U, IsAffineOpen U → Function.Bijective (φ.app U) := by sorry
