-- Prove2me | Theorems.Thm_GlobalTheory_PowUnif_exists_powUnif
-- name    : GlobalTheory.PowUnif.exists_powUnif
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:13.729745+00:00
-- url     : https://prove2.me/theorems/09755ae2-d1a7-49ef-b12b-bbf96198d794
-- title:
--   Pow Unif: exists pow Unif
-- statement:
--   The Pow Unif construction uses the exists pow Unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L286-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L286-L327

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowUnif
variable {G' G : Over (Sp ℂ)} [GrpObj G'] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G' G j)
variable {L : LB G.left} {g : ℕ} (u : HolUnif G L g)

theorem GlobalTheory.PowUnif.exists_powUnif (hL : L.IsLB) {L' : LB G'.left} (hL' : L'.IsLB) (w : LB.Iso L' (Out.boxLB L p.pr))
    (hw : w.IsGen) {n : ℕ} (e : Fin j × Fin g ≃ Fin n) :
    ∃ u' : HolUnif G' L' n, (∀ z, z ∈ u'.Λ ↔ ∀ i, blockPr e i z ∈ u.Λ) ∧
      (∀ z i, u'.ex z ≫ p.pr i = u.ex (blockPr e i z)) ∧
      ∀ jj b z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (Out.boxLB L p.pr).U jj → ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U b →
        ∏ i, u.fr (jj i) (blockPr e i z) =
          valAt' (u'.ex z).left ((Out.boxLB L p.pr).U jj ⊓ L'.U b) (w.s (jj, b)).val * u'.fr b z := by sorry
