-- Prove2me | Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_gen_two
-- name    : GlobalTheory.ArtinKernel.evalPt_gen_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:47.754166+00:00
-- url     : https://prove2.me/theorems/f92f2d04-e6ac-4ecc-ad05-575a45830603
-- title:
--   Artin Kernel: eval Pt gen two
-- statement:
--   The Artin Kernel construction uses the eval Pt gen two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnFamPtAffine.lean#L86-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnFamPtAffine.lean#L86-L105

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

theorem GlobalTheory.ArtinKernel.evalPt_gen_two (L : LB X) (φ₀ φ₁ : Y ⟶ X)
    (c : LB.Gen (LB.LinComb L (K := Fin 2) ![φ₀, φ₁] ![1, -1])) (hc : c.IsGen)
    (x : Sp R ⟶ Y) (y₀ y₁ : Sp R ⟶ X) (h₀ : x ≫ φ₀ = y₀) (h₁ : x ≫ φ₁ = y₁)
    (j j' : Fin 2 → L.ι) (a : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j) (b : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j')
    (a₀ : ⊤ ≤ y₀ ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j' 0))) (a₁ : ⊤ ≤ y₁ ⁻¹ᵁ (L.U (j 1) ⊓ L.U (j' 1))) :
    evalPt x _ a (c.s j).val * evalPt y₁ _ a₁ (L.g (j 1) (j' 1)).val =
      evalPt y₀ _ a₀ (L.g (j 0) (j' 0)).val * evalPt x _ b (c.s j').val := by sorry
