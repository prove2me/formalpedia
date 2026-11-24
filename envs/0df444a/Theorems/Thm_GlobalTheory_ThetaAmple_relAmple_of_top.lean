-- Prove2me | Theorems.Thm_GlobalTheory_ThetaAmple_relAmple_of_top
-- name    : GlobalTheory.ThetaAmple.relAmple_of_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:05:25.80894+00:00
-- url     : https://prove2.me/theorems/7edfca05-1d4d-4cd8-b743-2e14c1069dbb
-- title:
--   Theta Ample: rel Ample of top
-- statement:
--   The Theta Ample construction uses the rel Ample of top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L44-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RelAmpleThetaBundleProjectiveModel.lean#L44-L73

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAmple

theorem GlobalTheory.ThetaAmple.relAmple_of_top {X : Over (Sp ℂ)} {L : LB X.left}
    (h : ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ s : Fin (M + 1) → LB.Sec (Out.powOver X L ⊤ N),
      (⨆ i, Out.nonzeroLocus (s i) = ⊤) ∧
      ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧
        ∃ r : Fin (M + 1) → Γ((X.hom ⁻¹ᵁ ⊤).toScheme, Out.nonzeroLocus (s i)),
          (∀ j k, ((X.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ (Out.powOver X L ⊤ N).U k ≤ (Out.powOver X L ⊤ N).U k)).op).hom
                ((s j).f k) =
            ((X.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_left :
              Out.nonzeroLocus (s i) ⊓ (Out.powOver X L ⊤ N).U k ≤ Out.nonzeroLocus (s i))).op).hom (r j) *
            ((X.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ (Out.powOver X L ⊤ N).U k ≤ (Out.powOver X L ⊤ N).U k)).op).hom
                ((s i).f k)) ∧
          Function.Surjective (MvPolynomial.eval₂Hom
            ((X.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom r)) : Out.RelAmple X L := by sorry
