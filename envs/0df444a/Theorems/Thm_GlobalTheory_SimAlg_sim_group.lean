-- Prove2me | Theorems.Thm_GlobalTheory_SimAlg_sim_group
-- name    : GlobalTheory.SimAlg.sim_group
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:56.921144+00:00
-- url     : https://prove2.me/theorems/07c18206-3122-41ba-bfa8-effee5da1548
-- title:
--   Sim Alg: sim group
-- statement:
--   The Sim Alg construction uses the sim group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFormEqOne.lean#L134-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFormEqOne.lean#L134-L141

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFormEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SimAlg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem GlobalTheory.SimAlg.sim_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1) := by sorry
