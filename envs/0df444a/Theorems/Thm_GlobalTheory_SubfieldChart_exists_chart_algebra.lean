-- Prove2me | Theorems.Thm_GlobalTheory_SubfieldChart_exists_chart_algebra
-- name    : GlobalTheory.SubfieldChart.exists_chart_algebra
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:23:22.264844+00:00
-- url     : https://prove2.me/theorems/f5821b01-a593-454b-b107-95c09ac2411f
-- title:
--   Subfield Chart: exists chart algebra
-- statement:
--   The Subfield Chart construction uses the exists chart algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolomorphicChart.lean#L71-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolomorphicChart.lean#L71-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicChart
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
noncomputable section
open GlobalTheory GlobalTheory.SubfieldChart
variable {k A : Type} [Field k] [Algebra k ℂ] [CommRing A] [Algebra k A]

theorem GlobalTheory.SubfieldChart.exists_chart_algebra (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d k A]
    (e : A →ₐ[k] ℂ) :
    ∃ (W : Set (Fin d → ℂ)) (p : (Fin d → ℂ) → (A →ₐ[k] ℂ)) (n : ℕ) (r : Fin n → A) (ε : ℝ),
      IsOpen W ∧ 0 ∈ W ∧ p 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => p w a) W) ∧
      Set.InjOn p W ∧ ∀ x : A →ₐ[k] ℂ, (∀ i, ‖x (r i) - e (r i)‖ < ε) → ∃ w ∈ W, x = p w := by sorry
