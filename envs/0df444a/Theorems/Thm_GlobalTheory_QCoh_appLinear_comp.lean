-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_appLinear_comp
-- name    : GlobalTheory.QCoh.appLinear_comp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:49.437223+00:00
-- url     : https://prove2.me/theorems/dfa14d4e-b64f-59f2-91cd-59b2782b1ad1
-- title:
--   QCoh: app Linear comp
-- statement:
--   The QCoh construction uses the app Linear comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L27-L28

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

theorem GlobalTheory.QCoh.appLinear_comp (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) :
    appLinear (φ ≫ ψ) U = appLinear ψ U ∘ₗ appLinear φ U := by sorry
