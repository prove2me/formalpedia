-- Prove2me | Theorems.Thm_GlobalTheory_LocalWeightUnits_exists_units
-- name    : GlobalTheory.LocalWeightUnits.exists_units
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:40:15.505806+00:00
-- url     : https://prove2.me/theorems/47ec9b64-00dc-55d0-8daa-3acea0a5a40b
-- title:
--   Local Weight Units: exists units
-- statement:
--   The Local Weight Units construction uses the exists units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeightZeroSumOne.lean#L76-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeightZeroSumOne.lean#L76-L98

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

theorem GlobalTheory.LocalWeightUnits.exists_units {d : ℕ} {i : splitTorus S (Fin d → ℤ) ⟶ H} {V : H.left.Opens} (w : Fin d → Γ(H.left, V)ˣ)
    (hw : ∀ k, GlobalTheory.UU.IsWt i V (w k).val (Pi.single k 1)) :
    ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, V)ˣ, ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ := by sorry
