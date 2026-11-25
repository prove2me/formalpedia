-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_gen_unique_scal
-- name    : GlobalTheory.ConstFam.gen_unique_scal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:37:08.66283+00:00
-- url     : https://prove2.me/theorems/50dbe04a-b823-47b0-87c8-87666e631454
-- title:
--   Const Fam: gen unique scal
-- statement:
--   The Const Fam construction uses the gen unique scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/StalkMapInjectiveOfFlat.lean#L19-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/StalkMapInjectiveOfFlat.lean#L19-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

theorem GlobalTheory.ConstFam.gen_unique_scal {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) (c : Γ(S₀, ⊤))
    (h : ∀ y J, Good M y J → (val u e y J).val = gs (𝟙 _) y ⊤ c * (val u' e y J).val) (Z : Scheme.{0}) (r : Z ⟶ Y)
    (z : Z) (J) (hJ : Good M z J) : (val u r z J).val = gs (r ≫ p) z ⊤ c * (val u' r z J).val := by sorry
