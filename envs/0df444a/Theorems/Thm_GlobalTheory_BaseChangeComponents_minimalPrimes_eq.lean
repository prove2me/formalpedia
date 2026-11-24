-- Prove2me | Theorems.Thm_GlobalTheory_BaseChangeComponents_minimalPrimes_eq
-- name    : GlobalTheory.BaseChangeComponents.minimalPrimes_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:28.291969+00:00
-- url     : https://prove2.me/theorems/556d3b3b-9650-48fc-b997-334b2cfd3ab1
-- title:
--   Base Change Components: minimal Primes eq
-- statement:
--   The Base Change Components construction uses the minimal Primes eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsNoetherianRingTensor.lean#L65-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsNoetherianRingTensor.lean#L65-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsNoetherianRingTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.BaseChangeComponents
variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]

theorem GlobalTheory.BaseChangeComponents.minimalPrimes_eq (R : Subalgebra K Ω)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) :
    minimalPrimes (F ⊗[K] R) = Ideal.comap (incl F R) '' minimalPrimes (F ⊗[K] Ω) := by sorry
