-- Prove2me | Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_appLE
-- name    : GlobalTheory.ArtinKernel.evalPt_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:39.602924+00:00
-- url     : https://prove2.me/theorems/c92ba7a5-8831-4f9a-a7f9-c15c91af348d
-- title:
--   Artin Kernel: eval Pt app LE
-- statement:
--   The Artin Kernel construction uses the eval Pt app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnFamPtAffine.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnFamPtAffine.lean#L30-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] {X Y : Scheme.{0}}

theorem GlobalTheory.ArtinKernel.evalPt_appLE (x : Sp R ⟶ X) (φ : X ⟶ Y) (y : Sp R ⟶ Y) (hy : x ≫ φ = y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ φ ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (hU : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evalPt x V hV ((φ.appLE U V e).hom f) = evalPt y U hU f := by sorry
