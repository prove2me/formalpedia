-- Prove2me | Theorems.Thm_GlobalTheory_GenericValue_mem_range_of_fixed
-- name    : GlobalTheory.GenericValue.mem_range_of_fixed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:55:09.645243+00:00
-- url     : https://prove2.me/theorems/960413d4-3ad9-4bc3-85f2-911b75801228
-- title:
--   Generic Value: mem range of fixed
-- statement:
--   The Generic Value construction uses the mem range of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsAlgHomOfIsTranscendenceBasis.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsAlgHomOfIsTranscendenceBasis.lean#L45-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenericValue
open MvPolynomial
variable {K : Type} [Field K]

theorem GlobalTheory.GenericValue.mem_range_of_fixed [IsAlgClosed K] {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (a : Ω)
    (h : ∀ j : Ω →ₐ[K] Ω, j a = a) : a ∈ Set.range (algebraMap K Ω) := by sorry
