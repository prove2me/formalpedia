-- Prove2me | Theorems.Thm_GlobalTheory_ProjAffineLoci_chart
-- name    : GlobalTheory.ProjAffineLoci.chart
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:19:45.552994+00:00
-- url     : https://prove2.me/theorems/34f91f17-d36a-40fc-b333-ad39a0e52790
-- title:
--   Proj Affine Loci: chart
-- statement:
--   The Proj Affine Loci construction uses the chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NonzeroLocusSecPw.lean#L34-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NonzeroLocusSecPw.lean#L34-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NonzeroLocusSecPw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.ProjAffineLoci
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gs gs_res gs_mul fn_ext)
open TopologicalSpace
variable {X : Scheme.{0}} {R : Type} [CommRing R]

theorem GlobalTheory.ProjAffineLoci.chart (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (hH : H.IsLB) {I : Type} (t : I → LB.Sec H) (i : I)
    {W : X.Opens} (e : nonzeroLocus (t i) = W) {n : ℕ} (b : Fin n → Γ(X, W))
    (hb : Function.Surjective (MvPolynomial.eval₂Hom (cst f W) b)) (c : Fin n → I)
    (hc : ∀ l k, rs X (inf_le_right : W ⊓ H.U k ≤ H.U k) ((t (c l)).f k) =
      rs X (inf_le_left : W ⊓ H.U k ≤ W) (b l) * rs X (inf_le_right : W ⊓ H.U k ≤ H.U k) ((t i).f k)) :
    ∃ r : I → Γ(X, nonzeroLocus (t i)),
      (∀ j k, rs X (inf_le_right : nonzeroLocus (t i) ⊓ H.U k ≤ H.U k) ((t j).f k) =
        rs X (inf_le_left : nonzeroLocus (t i) ⊓ H.U k ≤ nonzeroLocus (t i)) (r j) *
          rs X (inf_le_right : nonzeroLocus (t i) ⊓ H.U k ≤ H.U k) ((t i).f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (cst f (nonzeroLocus (t i))) r) := by sorry
