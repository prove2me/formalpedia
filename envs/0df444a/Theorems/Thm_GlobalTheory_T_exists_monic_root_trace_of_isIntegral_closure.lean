-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_monic_root_trace_of_isIntegral_closure
-- name    : GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:56.598899+00:00
-- url     : https://prove2.me/theorems/937976af-8128-4e07-a4ef-6119f063bcbf
-- title:
--   T: exists monic root trace of is Integral closure
-- statement:
--   The T construction uses the exists monic root trace of is Integral closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TraceMonicOverMvPolynomialStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TraceMonicOverMvPolynomialStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceMonicOverMvPolynomial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceMonicOverMvPolynomialStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure : ∀ {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K] {ι : Type} (z : ι → K), (∀ i, z i ∈ F) → ∀ (v : K), IsIntegral (Subring.closure (Set.range z)) v → ∃ f : Polynomial (MvPolynomial ι ℤ), f.Monic ∧ f.eval₂ (aeval z).toRingHom (Algebra.trace F K v : K) = 0 := by sorry
