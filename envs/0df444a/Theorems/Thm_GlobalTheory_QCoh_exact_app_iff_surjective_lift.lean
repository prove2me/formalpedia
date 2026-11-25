-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_exact_app_iff_surjective_lift
-- name    : GlobalTheory.QCoh.exact_app_iff_surjective_lift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:17:25.897737+00:00
-- url     : https://prove2.me/theorems/b5b0d14a-a82e-46b3-9e2a-53cc6158f542
-- title:
--   QCoh: exact app iff surjective lift
-- statement:
--   The QCoh construction uses the exact app iff surjective lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L320-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L320-L331

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

theorem GlobalTheory.QCoh.exact_app_iff_surjective_lift (S : ShortComplex X.Modules) (U : X.Opens) :
    Function.Exact (S.f.app U) (S.g.app U) ↔
      Function.Surjective ((kernel.lift S.g S.f S.zero).app U) := by sorry
