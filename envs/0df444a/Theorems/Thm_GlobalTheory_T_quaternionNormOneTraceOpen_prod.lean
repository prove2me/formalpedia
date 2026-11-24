-- Prove2me | Theorems.Thm_GlobalTheory_T_quaternionNormOneTraceOpen_prod
-- name    : GlobalTheory.T.quaternionNormOneTraceOpen_prod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:57:00.366174+00:00
-- url     : https://prove2.me/theorems/169a7487-da68-4a67-a1b4-25607a91a7cd
-- title:
--   T: quaternion Norm One Trace Open prod
-- statement:
--   The T construction uses the quaternion Norm One Trace Open prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProdStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProdStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenProd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenProdStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.quaternionNormOneTraceOpen_prod : ∀ (R₁ R₂ : Type) [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂] (a₁ b₁ : R₁) (a₂ b₂ : R₂), TraceOpen R₁ a₁ b₁ → TraceOpen R₂ a₂ b₂ → TraceOpen (R₁ × R₂) (a₁, a₂) (b₁, b₂) := by sorry
