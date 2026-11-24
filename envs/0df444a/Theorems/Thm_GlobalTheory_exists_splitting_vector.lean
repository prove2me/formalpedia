-- Prove2me | Theorems.Thm_GlobalTheory_exists_splitting_vector
-- name    : GlobalTheory.exists_splitting_vector
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:18.594939+00:00
-- url     : https://prove2.me/theorems/3737259d-854c-4be2-b051-e24020514482
-- title:
--   Global Theory: exists splitting vector
-- statement:
--   The Global Theory construction uses the exists splitting vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsSmulMemOfMemSpanFraction.lean#L28-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsSmulMemOfMemSpanFraction.lean#L28-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem GlobalTheory.exists_splitting_vector {V : Type} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (Λ : Submodule R V) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set V) = ⊤) (l : V →ₗ[K] K) (hl : l ≠ 0) :
    ∃ (c : FractionalIdeal R⁰ K) (e : V), c ≠ 0 ∧ l e = 1 ∧ (∀ v ∈ Λ, l v ∈ c) ∧
      ∀ x ∈ c, x • e ∈ Λ := by sorry
