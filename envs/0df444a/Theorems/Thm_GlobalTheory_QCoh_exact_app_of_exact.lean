-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_exact_app_of_exact
-- name    : GlobalTheory.QCoh.exact_app_of_exact
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:17:24.343577+00:00
-- url     : https://prove2.me/theorems/0a1020a9-375b-4f33-96a2-7495a8ceb164
-- title:
--   QCoh: exact app of exact
-- statement:
--   The QCoh construction uses the exact app of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L333-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L333-L337

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

theorem GlobalTheory.QCoh.exact_app_of_exact {S : ShortComplex X.Modules} (hS : S.Exact) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] (hU : IsAffineOpen U) :
    Function.Exact (S.f.app U) (S.g.app U) := by sorry
