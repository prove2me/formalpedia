-- Prove2me | Theorems.Thm_GlobalTheory_QSA_TraceOpenProd_continuous_coord
-- name    : GlobalTheory.QSA.TraceOpenProd.continuous_coord
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:03:41.467311+00:00
-- url     : https://prove2.me/theorems/f790b33d-ed56-4422-9603-5311fc6edecf
-- title:
--   Trace Open Prod: continuous coord
-- statement:
--   The Trace Open Prod construction uses the continuous coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProd.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProd.lean#L35-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA GlobalTheory.QSA.TraceOpenProd
variable {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂]
  {a₁ b₁ : R₁} {a₂ b₂ : R₂}

theorem GlobalTheory.QSA.TraceOpenProd.continuous_coord {R : Type} [CommRing R] [TopologicalSpace R] {a b : R} (i : Fin 4) :
    Continuous (fun x : ℍ[R, a, b] => coords x i) := by sorry
