-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_maximalIdeal_pow_iff_normalizedValuation
-- name    : GroundTheory.LocalField.mem_maximalIdeal_pow_iff_normalizedValuation
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:46.451697+00:00
-- url     : https://prove2.me/theorems/f7cb9a1f-5f63-4003-ae0e-a5e4443bcdea
-- title:
--   Local Field: mem maximal Ideal pow iff normalized Valuation
-- statement:
--   The Local Field construction uses the mem maximal Ideal pow iff normalized Valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L103-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L103-L111

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_Ramification
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
open ValuativeRel IsLocalRing
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L)
variable {K L}

theorem GroundTheory.LocalField.mem_maximalIdeal_pow_iff_normalizedValuation (n : ℕ) (y : 𝒪[L]) :
    y ∈ 𝓂[L] ^ n ↔ normalizedValuation L (y : L) ≤ WithZero.exp (-(n : ℤ)) := by sorry
