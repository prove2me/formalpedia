-- Prove2me | Theorems.Thm_GlobalTheory_BaseChangeComponents_isNoetherianRing_tensor
-- name    : GlobalTheory.BaseChangeComponents.isNoetherianRing_tensor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:26.934451+00:00
-- url     : https://prove2.me/theorems/4e134ca0-97d5-4afb-99ae-3322de6c744f
-- title:
--   Base Change Components: is Noetherian Ring tensor
-- statement:
--   The Base Change Components construction uses the is Noetherian Ring tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsNoetherianRingTensor.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsNoetherianRingTensor.lean#L78-L85

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

theorem GlobalTheory.BaseChangeComponents.isNoetherianRing_tensor (R : Subalgebra K Ω) (hfg : R.FG)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) : IsNoetherianRing (F ⊗[K] Ω) := by sorry
