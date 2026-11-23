-- Prove2me | Theorems.Thm_GroundTheory_LocalField_smodEq_iff_pow_dvd
-- name    : GroundTheory.LocalField.smodEq_iff_pow_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:08.094576+00:00
-- url     : https://prove2.me/theorems/27266d23-cf65-4af6-88fa-438f0f24974a
-- title:
--   Local Field: smod Eq iff pow dvd
-- statement:
--   The Local Field construction uses the smod Eq iff pow dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L224-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L224-L226

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

theorem GroundTheory.LocalField.smodEq_iff_pow_dvd {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} {x y : 𝒪[K]} :
    x ≡ y [SMOD (𝓂[K] ^ n • ⊤ : Submodule 𝒪[K] 𝒪[K])] ↔ π ^ n ∣ x - y := by sorry
