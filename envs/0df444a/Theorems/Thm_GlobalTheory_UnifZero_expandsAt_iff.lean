-- Prove2me | Theorems.Thm_GlobalTheory_UnifZero_expandsAt_iff
-- name    : GlobalTheory.UnifZero.expandsAt_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:00:45.265986+00:00
-- url     : https://prove2.me/theorems/2eafed64-6d81-4dcf-bfb1-bde4b6b92aa0
-- title:
--   Unif Zero: expands At iff
-- statement:
--   The Unif Zero construction uses the expands At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqOfSecConst.lean#L218-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqOfSecConst.lean#L218-L265

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UnifZero
open GlobalTheory.ToricData
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R)
variable {R I}

theorem GlobalTheory.UnifZero.expandsAt_iff (e k : ℕ)
    {σ : LB.Sec (LB.LinComb (zeroPre R I).LG.L (K := Fin 1)
      (fun _ => 𝟙 (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (fun _ => (k : ℤ)))}
    {f : ∀ α : (zeroData R I).toPre.X, (zeroData R I).toPre.SecB k α} {a b : R}
    (ha : SecConst σ (scal (𝟙 _) a)) (hb : SecConst (f PUnit.unit) (scal (𝟙 _) b)) :
    (zeroPre R I).ExpandsAt e k σ f ↔ a - b ∈ I ^ (e + 1) := by sorry
