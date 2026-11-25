-- Prove2me | Theorems.Thm_GlobalTheory_ThetaBaseChange_exists_side
-- name    : GlobalTheory.ThetaBaseChange.exists_side
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:59:34.905843+00:00
-- url     : https://prove2.me/theorems/35440d42-3ee1-4c80-a5f6-b4ec4c912a36
-- title:
--   Theta Base Change: exists side
-- statement:
--   The Theta Base Change construction uses the exists side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfPush.lean#L50-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfPush.lean#L50-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
variable {Y Y' X X' N N' : Scheme.{0}} {L : LB X} {L' : LB X'} {M : LB N} {M' : LB N'}

theorem GlobalTheory.ThetaBaseChange.exists_side (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB) (hM' : M'.IsLB)
    {c₀ : Y ⟶ X} {q : Y ⟶ N} {w : LB.Iso (L.pull c₀) (M.pull q)} (hw : w.IsGen) (n : X ⟶ Y) (hn : n ≫ c₀ = 𝟙 X)
    {c₁ : Y' ⟶ X'} {q' : Y' ⟶ N'} {w' : LB.Iso (L'.pull c₁) (M'.pull q')} (hw' : w'.IsGen)
    {Ψ : N' ⟶ N} {wM : LB.Iso M' (M.pull Ψ)} (hwM : wM.IsGen) (Φ : Y' ⟶ X) (hΦ : Φ ≫ n ≫ q = q' ≫ Ψ) :
    ∃ v : LB.Iso (L'.pull c₁) (L.pull Φ), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (z : Z) (j : M.ι) (j' : M'.ι) (i : L.ι) (i' : L'.ι),
        Ψ (q' (f z)) ∈ M.U j → q' (f z) ∈ M'.U j' → Φ (f z) ∈ L.U i → c₁ (f z) ∈ L'.U i' →
        isoVal w (f ≫ Φ ≫ n) z j i * isoVal v f z i i' = gw wM (f ≫ q') z j j' * isoVal w' f z j' i' := by sorry
