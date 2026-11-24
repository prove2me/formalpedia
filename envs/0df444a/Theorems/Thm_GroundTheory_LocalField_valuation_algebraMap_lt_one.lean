-- Prove2me | Theorems.Thm_GroundTheory_LocalField_valuation_algebraMap_lt_one
-- name    : GroundTheory.LocalField.valuation_algebraMap_lt_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:46:49.360001+00:00
-- url     : https://prove2.me/theorems/7ad7a385-1b17-4ede-a0ca-0c5b50d723b0
-- title:
--   Local Field: valuation algebra Map lt one
-- statement:
--   The Local Field construction uses the valuation algebra Map lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L367-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L367-L370

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
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
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
omit [FiniteDimensional K L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem GroundTheory.LocalField.valuation_algebraMap_lt_one {π : 𝒪[K]} (hπ : Irreducible π) :
    valuation L (algebraMap K L (π : K)) < 1 := by sorry
