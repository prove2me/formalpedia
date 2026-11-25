-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_Core_Test_exists_isGt_fibre
-- name    : GlobalTheory.ZJ.Core.Test.exists_isGt_fibre
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:29:28.673806+00:00
-- url     : https://prove2.me/theorems/602476f6-02cf-4244-9c8c-4df5efd42f05
-- title:
--   Test: exists is Gt fibre
-- statement:
--   The Test construction uses the exists is Gt fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FibreLawOfTestCartesian.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FibreLawOfTestCartesian.lean#L48-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusPointEqOneOfAxes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FibreLawOfTestCartesian
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
open GlobalTheory GlobalTheory.ZJ

theorem GlobalTheory.ZJ.Core.Test.exists_isGt_fibre {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (K : Type) [Field K] (r : Sp K ⟶ Sp τ.V) (hr : Set.range r = {IsLocalRing.closedPoint τ.V}) :
    ∃ (G₁ : Over (Sp K)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (E : SplitExt (Sp K)) (φ : G₁.left ⟶ τ.H.left),
      E.IsGt G₁ ∧ IsGrpPullback G₁ τ.H r φ := by sorry
