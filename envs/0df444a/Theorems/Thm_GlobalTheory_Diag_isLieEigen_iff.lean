-- Prove2me | Theorems.Thm_GlobalTheory_Diag_isLieEigen_iff
-- name    : GlobalTheory.Diag.isLieEigen_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:28:23.915664+00:00
-- url     : https://prove2.me/theorems/429e03f7-b262-426c-9092-2906b72f2063
-- title:
--   Diag: is Lie Eigen iff
-- statement:
--   The Diag construction uses the is Lie Eigen iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LeftEqIffLieVecSmul.lean#L447-L467
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LeftEqIffLieVecSmul.lean#L447-L467

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent IsLieComb IsLieBasis OAct epsPt
  IsLieEigen LieMult)
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.Diag
variable {S : Scheme.{0}} {k : Type} [Field k] (t : Sp k ⟶ S) {O : Type} [CommRing O]
  {X : Type} [AddCommGroup X] [Module O X] (τ : O →+* k)

theorem GlobalTheory.Diag.isLieEigen_iff (v : epsPt t ⟶ splitTorus S X) :
    IsLieEigen (diagAct S O X) t τ v ↔
      ∃ c : X →+ k, epsVec _ c = v ∧ ∀ (a : O) (x : X), c (a • x) = τ a * c x := by sorry
