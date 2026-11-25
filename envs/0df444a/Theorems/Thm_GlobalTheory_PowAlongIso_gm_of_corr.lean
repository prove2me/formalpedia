-- Prove2me | Theorems.Thm_GlobalTheory_PowAlongIso_gm_of_corr
-- name    : GlobalTheory.PowAlongIso.gm_of_corr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:25:04.310687+00:00
-- url     : https://prove2.me/theorems/4ff924d3-073d-4520-b1b6-e1770cf69e27
-- title:
--   Pow Along Iso: gm of corr
-- statement:
--   The Pow Along Iso construction uses the gm of corr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L113-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L113-L126

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

theorem GlobalTheory.PowAlongIso.gm_of_corr (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ}
    {h : Y' ⟶ Y} (hφ : ∀ k, φ' k = h ≫ φ k) {t : LB.Gen (LB.LinComb M φ ε)} {t' : LB.Gen (LB.LinComb M φ' ε)}
    (ht : t.IsGen) (ht' : t'.IsGen) (H : LB.Gen.Corr M _ _ _ _ t' (LB.pullGen M φ ε t h)) (r : Z ⟶ Y') (z : Z)
    {a : K → M.ι} (ha : r z ∈ LB.wchart M φ' a) :
    gm r z (LB.wchart M φ' a) (t'.s a) = gm (r ≫ h) z (LB.wchart M φ a) (t.s a) := by sorry
