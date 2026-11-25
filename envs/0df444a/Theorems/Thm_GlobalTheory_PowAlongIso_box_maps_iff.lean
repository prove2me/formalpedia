-- Prove2me | Theorems.Thm_GlobalTheory_PowAlongIso_box_maps_iff
-- name    : GlobalTheory.PowAlongIso.box_maps_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:21:12.093146+00:00
-- url     : https://prove2.me/theorems/2f2f4637-fbf0-4b5c-93dd-fb6b934dbe5c
-- title:
--   Pow Along Iso: box maps iff
-- statement:
--   The Pow Along Iso construction uses the box maps iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L128-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L128-L159

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

theorem GlobalTheory.PowAlongIso.box_maps_iff (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K]
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε))
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) :
    LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM →
      ∏ i, gm (r ≫ ρ i) z (LB.wchart M (φ i) (fun a => jN a i)) ((t i).s (fun a => jN a i)) =
        (∏ a, bw w (r ≫ φ' a) z (jN a) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) := by sorry
