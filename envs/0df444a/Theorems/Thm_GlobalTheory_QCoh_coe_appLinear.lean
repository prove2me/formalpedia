-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_coe_appLinear
-- name    : GlobalTheory.QCoh.coe_appLinear
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:34.797675+00:00
-- url     : https://prove2.me/theorems/9368d127-547d-5ec2-bef1-94fd3040bfae
-- title:
--   QCoh: coe app Linear
-- statement:
--   The QCoh construction uses the coe app Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L25-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L25-L25

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

theorem GlobalTheory.QCoh.coe_appLinear (φ : M ⟶ N) (U : X.Opens) : ⇑(appLinear φ U) = φ.app U := by sorry
