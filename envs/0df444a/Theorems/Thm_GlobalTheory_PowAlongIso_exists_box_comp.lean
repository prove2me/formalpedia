-- Prove2me | Theorems.Thm_GlobalTheory_PowAlongIso_exists_box_comp
-- name    : GlobalTheory.PowAlongIso.exists_box_comp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:19:05.229206+00:00
-- url     : https://prove2.me/theorems/c6be76cb-56e0-45c2-961c-abee2b5112ed
-- title:
--   Pow Along Iso: exists box comp
-- statement:
--   The Pow Along Iso construction uses the exists box comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L57-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L57-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf

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
open GlobalTheory GlobalTheory.PowAlongIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR (bw gm_linCombIso mem_finf)
variable {X X' X'' Y Y' Y₀ Z : Scheme.{0}}
variable {M : LB X} {M' : LB X'} {M'' : LB X''} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem GlobalTheory.PowAlongIso.exists_box_comp (hM : M.IsLB) (hM' : M'.IsLB) (hM'' : M''.IsLB) {E : X'' ⟶ X'} {pr' : Fin j → (X'' ⟶ X)}
    (hpr : ∀ i, pr' i = E ≫ pr i) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen)
    (w' : LB.Iso M'' (M'.pull E)) (hw' : w'.IsGen) :
    ∃ w'' : LB.Iso M'' (LB.LinComb M pr' (fun _ => 1)), w''.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z)
      (a : Fin j → M.ι) (b : M'.ι) (c : M''.ι), f z ∈ LB.wchart M pr' a → E (f z) ∈ M'.U b → f z ∈ M''.U c →
      bw w'' f z a c = bw w (f ≫ E) z a b * gw w' f z b c := by sorry
