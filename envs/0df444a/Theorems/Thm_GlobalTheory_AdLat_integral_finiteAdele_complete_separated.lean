-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_integral_finiteAdele_complete_separated
-- name    : GlobalTheory.AdLat.integral_finiteAdele_complete_separated
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:08:40.636707+00:00
-- url     : https://prove2.me/theorems/8eac61b3-97a7-491c-9894-e10da8cfe9b1
-- title:
--   Ad Lat: integral finite Adele complete separated
-- statement:
--   The Ad Lat construction uses the integral finite Adele complete separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralFiniteAdeleCompleteSeparated.lean#L71-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralFiniteAdeleCompleteSeparated.lean#L71-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralFiniteAdeleCompleteSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat WithZero
open scoped TensorProduct Matrix nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.AdLat
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.AdLat.integral_finiteAdele_complete_separated :
    ∀ (F : Type) [Field F] [NumberField F], (∀ y : FiniteAdeleRing (𝓞 F) F, (∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = N • a) → y = 0) ∧ ∀ x : ℕ → FiniteAdeleRing (𝓞 F) F, (∀ N v, x N v ∈ v.adicCompletionIntegers F) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ x (N * m) = x N + N • a) → ∃ y : FiniteAdeleRing (𝓞 F) F, ∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = x N + N • a := by sorry
