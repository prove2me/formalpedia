-- Prove2me | Theorems.Thm_GlobalTheory_hermForm_principal_dim_one
-- name    : GlobalTheory.hermForm_principal_dim_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:43.023319+00:00
-- url     : https://prove2.me/theorems/30047c78-237b-4166-a6a9-f20b56074016
-- title:
--   Global Theory: herm Form principal dim one
-- statement:
--   The Global Theory construction uses the herm Form principal dim one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPrincipalDimOne.lean#L12-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPrincipalDimOne.lean#L12-L131

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_PureTypeVectorSpansQuadraticLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPrincipalDimOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open PureTypeVector

theorem GlobalTheory.hermForm_principal_dim_one :
  ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (w : Fin g → ℂ) (L : PeriodPair) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ), g = 1 → w ≠ 0 → (∀ z : ℂ, z ∈ L.lattice ↔ z • w ∈ Λ) → Hm.IsHermitian → 0 < (hermForm Hm w w).re → (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∀ z z' : ℂ, hermForm Hm (z • w) (z' • w) = z * starRingEnd ℂ z' / (|(L.ω₁ * starRingEnd ℂ L.ω₂).im| : ℝ) := by sorry
