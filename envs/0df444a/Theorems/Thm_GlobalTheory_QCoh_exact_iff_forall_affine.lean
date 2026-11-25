-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_exact_iff_forall_affine
-- name    : GlobalTheory.QCoh.exact_iff_forall_affine
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:36.220118+00:00
-- url     : https://prove2.me/theorems/7694585a-8c98-4aae-9eb7-4362f4e435d9
-- title:
--   QCoh: exact iff forall affine
-- statement:
--   The QCoh construction uses the exact iff forall affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L646-L649
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L646-L649

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
variable (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
  [S.X₃.IsQuasicoherent]

theorem GlobalTheory.QCoh.exact_iff_forall_affine :
    S.Exact ↔ ∀ U, IsAffineOpen U → Function.Exact (S.f.app U) (S.g.app U) := by sorry
