-- Prove2me | Theorems.Thm_GroundTheory_LocalField_natCard_units_quotient_range_normUnits
-- name    : GroundTheory.LocalField.natCard_units_quotient_range_normUnits
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:10.138802+00:00
-- url     : https://prove2.me/theorems/32cbe810-e800-4028-98d1-3feeb621f9bf
-- title:
--   Local Field: nat Card units quotient range norm Units
-- statement:
--   The Local Field construction uses the nat Card units quotient range norm Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocal.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocal.lean#L76-L79

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsGalois K L] {σ : L ≃ₐ[K] L}
variable [IsCyclic (L ≃ₐ[K] L)]

theorem GroundTheory.LocalField.natCard_units_quotient_range_normUnits :
    Nat.card (Kˣ ⧸ (normUnits K L).range) = Module.finrank K L := by sorry
