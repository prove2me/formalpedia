-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_lowerRamificationGroupReal_of_lowerIndex_le
-- name    : GroundTheory.LocalField.mem_lowerRamificationGroupReal_of_lowerIndex_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:33.150511+00:00
-- url     : https://prove2.me/theorems/66efff27-056f-49dc-8844-f911b05e76b9
-- title:
--   Local Field: mem lower Ramification Group Real of lower Index le
-- statement:
--   The Local Field construction uses the mem lower Ramification Group Real of lower Index le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L67-L71

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Definitions.Def_GroundTheory_LocalFields_UpperNumbering
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.mem_lowerRamificationGroupReal_of_lowerIndex_le {t : ℝ} {σ σ' : L ≃ₐ[K] L}
    (h : σ ∈ lowerRamificationGroupReal K L t) (hle : lowerIndex K L σ ≤ lowerIndex K L σ') :
    σ' ∈ lowerRamificationGroupReal K L t := by sorry
