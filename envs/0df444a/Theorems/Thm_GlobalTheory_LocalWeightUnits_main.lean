-- Prove2me | Theorems.Thm_GlobalTheory_LocalWeightUnits_main
-- name    : GlobalTheory.LocalWeightUnits.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:44:05.387301+00:00
-- url     : https://prove2.me/theorems/24717379-b9a1-5be8-9494-120fdcd2317b
-- title:
--   Local Weight Units: main
-- statement:
--   The Local Weight Units construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeightZeroSumOne.lean#L107-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeightZeroSumOne.lean#L107-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightZeroSumOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.LocalWeightUnits
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ H}

theorem GlobalTheory.LocalWeightUnits.main : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), C.Torus c i → ∀ (a) (x : H.left), x ∈ C.W a → ∃ b : Γ(H.left, C.W a), HasWt i (C.W a) b 0 ∧ x ∈ H.left.basicOpen b ∧ Stable i (H.left.basicOpen b) ∧ ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, H.left.basicOpen b)ˣ, ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ := by sorry
