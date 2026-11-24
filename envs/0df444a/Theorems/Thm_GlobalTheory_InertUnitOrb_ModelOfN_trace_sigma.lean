-- Prove2me | Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_trace_sigma
-- name    : GlobalTheory.InertUnitOrb.ModelOfN.trace_sigma
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:54:58.079578+00:00
-- url     : https://prove2.me/theorems/eb4d951a-2b56-46dc-a9b3-e1c62f824a9f
-- title:
--   Model Of N: trace sigma
-- statement:
--   The Model Of N construction uses the trace sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L13-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L13-L46

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

theorem GlobalTheory.InertUnitOrb.ModelOfN.trace_sigma {K : UQ} (B : InvAlg K) (w : B.A) :
    Algebra.trace K.E B.A (B.σ w) = K.c (Algebra.trace K.E B.A w) := by sorry
