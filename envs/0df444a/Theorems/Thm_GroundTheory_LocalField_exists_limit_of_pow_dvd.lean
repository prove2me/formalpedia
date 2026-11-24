-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_limit_of_pow_dvd
-- name    : GroundTheory.LocalField.exists_limit_of_pow_dvd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:03.061148+00:00
-- url     : https://prove2.me/theorems/0d150803-7024-4dc4-8e37-168b0aaa4710
-- title:
--   Local Field: exists limit of pow dvd
-- statement:
--   The Local Field construction uses the exists limit of pow dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L230-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L230-L246

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
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
omit [FiniteDimensional K L]

theorem GroundTheory.LocalField.exists_limit_of_pow_dvd {π : 𝒪[K]} (hπ : Irreducible π) (c : ℕ → 𝒪[K])
    (hc : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, π ^ N ∣ c n - c m) :
    ∃ a, ∀ N, ∃ M, ∀ n ≥ M, π ^ N ∣ c n - a := by sorry
