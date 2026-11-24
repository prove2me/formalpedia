-- Prove2me | Theorems.Thm_GlobalTheory_ArtinKernel_differentiableOn_famPt
-- name    : GlobalTheory.ArtinKernel.differentiableOn_famPt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:58:48.452802+00:00
-- url     : https://prove2.me/theorems/4cf70722-fe6a-43aa-8cbf-5093aad2dd20
-- title:
--   Artin Kernel: differentiable On fam Pt
-- statement:
--   The Artin Kernel construction uses the differentiable On fam Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnFamPtAffine.lean#L311-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnFamPtAffine.lean#L311-L330

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
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {A : Over (Sp ℂ)}
variable [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
variable [Module.Finite ℂ R]

theorem GlobalTheory.ArtinKernel.differentiableOn_famPt {U : A.left.Opens} {V : (spO R ⊗ A).left.Opens}
    (hV : (snd (spO R) A).left ⁻¹ᵁ U ≤ V) (f : Γ((spO R ⊗ A).left, V)) (lam : R →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => lam (evalPt' (R := R) (famPt u R z).left V f))
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} := by sorry
