-- Prove2me | Theorems.Thm_GlobalTheory_TensHead_ker_map_mkQ_le
-- name    : GlobalTheory.TensHead.ker_map_mkQ_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:59.483277+00:00
-- url     : https://prove2.me/theorems/f7e8e42d-0c96-44ec-a990-ed70d46f9e7f
-- title:
--   Tens Head: ker map mk Q le
-- statement:
--   The Tens Head construction uses the ker map mk Q le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleOverStableSubmoduleTensorPureKernelSpan.lean#L32-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleOverStableSubmoduleTensorPureKernelSpan.lean#L32-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleTensorProductOperatorStableCountableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead

theorem GlobalTheory.TensHead.ker_map_mkQ_le {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁]
    [Module ℂ V₁] (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁) :
    LinearMap.ker (TensorProduct.map K₀.mkQ K₁.mkQ) ≤ tensKer K₀ K₁ := by sorry
