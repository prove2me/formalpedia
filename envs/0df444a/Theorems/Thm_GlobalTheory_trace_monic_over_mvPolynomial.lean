-- Prove2me | Theorems.Thm_GlobalTheory_trace_monic_over_mvPolynomial
-- name    : GlobalTheory.trace_monic_over_mvPolynomial
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:48.600611+00:00
-- url     : https://prove2.me/theorems/6e89d156-d243-43b5-a374-00194c00c84b
-- title:
--   Global Theory: trace monic over mv Polynomial
-- statement:
--   The Global Theory construction uses the trace monic over mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TraceMonicOverMvPolynomial.lean#L6-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TraceMonicOverMvPolynomial.lean#L6-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceMonicOverMvPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory

theorem GlobalTheory.trace_monic_over_mvPolynomial {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K]
    {ι : Type} (z : ι → K) (hz : ∀ i, z i ∈ F) (v : K)
    (hv : IsIntegral (Subring.closure (Set.range z)) v) :
    ∃ f : Polynomial (MvPolynomial ι ℤ), f.Monic ∧
      f.eval₂ (aeval z).toRingHom (Algebra.trace F K v : K) = 0 := by sorry
