-- Prove2me | Theorems.Thm_GlobalTheory_UnifJac_fderiv_val
-- name    : GlobalTheory.UnifJac.fderiv_val
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:25.594675+00:00
-- url     : https://prove2.me/theorems/ddf81c1d-ed2a-402c-8b7c-11d037591987
-- title:
--   Unif Jac: fderiv val
-- statement:
--   The Unif Jac construction uses the fderiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/UnifValueJacZeros.lean#L86-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/UnifValueJacZeros.lean#L86-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnifValueJacZeros
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
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.UnifJac
variable {A : Over (Sp ℂ)} [GrpObj A]
variable {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem GlobalTheory.UnifJac.fderiv_val (c : L.ι) (f : Γ(A.left, L.U c)) (F : (Fin g → ℂ) → ℂ) (hF : Differentiable ℂ F) (n : ℕ)
    (hf : ∀ y, ⊤ ≤ (u.ex y).left ⁻¹ᵁ L.U c → valAt' (u.ex y).left (L.U c) f = F y * u.fr c y ^ n)
    (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U c) (h0 : F z = 0) (w : Fin g → ℂ) :
    fderiv ℂ (fun y => valAt' (u.ex y).left (L.U c) f) z w = u.fr c z ^ n * fderiv ℂ F z w := by sorry
