-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_zero_of_forall_pow_dvd
-- name    : GroundTheory.LocalField.eq_zero_of_forall_pow_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:09.527227+00:00
-- url     : https://prove2.me/theorems/f190eb72-f73f-4b9d-8349-674e1cddfe1e
-- title:
--   Local Field: eq zero of forall pow dvd
-- statement:
--   The Local Field construction uses the eq zero of forall pow dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L250-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L250-L254

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

theorem GroundTheory.LocalField.eq_zero_of_forall_pow_dvd {π : 𝒪[K]} (hπ : Irreducible π) {x : 𝒪[K]}
    (h : ∀ N, π ^ N ∣ x) : x = 0 := by sorry
