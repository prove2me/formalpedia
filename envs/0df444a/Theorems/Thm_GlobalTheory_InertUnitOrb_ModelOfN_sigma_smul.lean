-- Prove2me | Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_sigma_smul
-- name    : GlobalTheory.InertUnitOrb.ModelOfN.sigma_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:15:51.191868+00:00
-- url     : https://prove2.me/theorems/39e28cae-7ed3-4983-b84e-43e7bf5fad47
-- title:
--   Model Of N: sigma smul
-- statement:
--   The Model Of N construction uses the sigma smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN

theorem GlobalTheory.InertUnitOrb.ModelOfN.sigma_smul {K : UQ} (B : InvAlg K) (e : K.E) (y : B.A) : B.σ (e • y) = K.c e • B.σ y := by sorry
