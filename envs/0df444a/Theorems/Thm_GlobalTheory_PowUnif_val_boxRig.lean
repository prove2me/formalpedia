-- Prove2me | Theorems.Thm_GlobalTheory_PowUnif_val_boxRig
-- name    : GlobalTheory.PowUnif.val_boxRig
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:53:27.012338+00:00
-- url     : https://prove2.me/theorems/1c367264-f5c8-4155-ae7f-f3ce6cf8ac5c
-- title:
--   Pow Unif: val box Rig
-- statement:
--   The Pow Unif construction uses the val box Rig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L358-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsHolomorphicUniformisationPowerThetaKeyDatu.lean#L358-L381

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

theorem GlobalTheory.PowUnif.val_boxRig {G' G : Over (Sp ℂ)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] {j : ℕ}
    (p : Out.IsPowGrp G' G j) {L : LB G.left} {L' : LB G'.left} (w : LB.Iso L' (Out.boxLB L p.pr))
    (r : LB.Gen (L.pull (eSec G))) (r' : LB.Gen (L'.pull (eSec G')))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) r' (Out.boxRig p L r))
    (a : L.ι) (b : (L'.pull (eSec G')).ι) (ha : ⊤ ≤ eSec G' ⁻¹ᵁ (Out.boxLB L p.pr).U fun _ => a)
    (hb : ⊤ ≤ (L'.pull (eSec G')).U b) :
    ∏ _i : Fin j, valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec G)).U fun _ => a) (r.s fun _ => a).val =
      valAt' (eSec G') ((Out.boxLB L p.pr).U (fun _ => a) ⊓ L'.U (b PUnit.unit)) (w.s (fun _ => a, b PUnit.unit)).val *
        valAt' (𝟙 (Sp ℂ)) ((L'.pull (eSec G')).U b) (r'.s b).val := by sorry
