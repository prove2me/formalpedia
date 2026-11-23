-- Prove2me | Theorems.Thm_GlobalTheory_exists_systemOfParameters_insert
-- name    : GlobalTheory.exists_systemOfParameters_insert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:52.716817+00:00
-- url     : https://prove2.me/theorems/285e1847-f9f4-4c04-8507-436964a4301f
-- title:
--   Global Theory: exists system Of Parameters insert
-- statement:
--   The Global Theory construction uses the exists system Of Parameters insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsSystemOfParametersInsert.lean#L6-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsSystemOfParametersInsert.lean#L6-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSystemOfParametersInsert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.exists_systemOfParameters_insert (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] (a : S) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal S) :
    ∃ (n : ℕ) (x : Fin n → S), (∀ i, x i ∈ maximalIdeal S) ∧
      ringKrullDim S = (n : WithBot ℕ∞) + 1 ∧
      ∃ N : ℕ, maximalIdeal S ^ N ≤ Ideal.span (insert a (Set.range x)) := by sorry
