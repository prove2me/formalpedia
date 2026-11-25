-- Prove2me | Theorems.Thm_GlobalTheory_PowAlongIso_box_maps_pull
-- name    : GlobalTheory.PowAlongIso.box_maps_pull
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:19:11.086041+00:00
-- url     : https://prove2.me/theorems/927ee2ec-df07-438b-aecb-344990a131b3
-- title:
--   Pow Along Iso: box maps pull
-- statement:
--   The Pow Along Iso construction uses the box maps pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L161-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L161-L177

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

theorem GlobalTheory.PowAlongIso.box_maps_pull (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K]
    {φ₁ : K → (Y ⟶ X')} {φ₂ : K → (Y' ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ₁ : Fin j → (Y ⟶ Y₀)}
    {ρ₂ : Fin j → (Y' ⟶ Y₀)} {h : Y' ⟶ Y} (hφ : ∀ a, φ₂ a = h ≫ φ₁ a) (hρ : ∀ i, ρ₂ i = h ≫ ρ₁ i)
    (hψ₁ : ∀ i a, φ₁ a ≫ pr i = ρ₁ i ≫ φ i a) (hψ₂ : ∀ i a, φ₂ a ≫ pr i = ρ₂ i ≫ φ i a)
    {t₁ : LB.Gen (LB.LinComb M' φ₁ ε)} {t₂ : LB.Gen (LB.LinComb M' φ₂ ε)} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen)
    (hc : LB.Gen.Corr M' _ _ _ _ t₂ (LB.pullGen M' φ₁ ε t₁ h)) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ₁ ε) t₁
      (GeneratorPullback.boxGen M pr φ₁ ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ₁ i) (φ i) ε φ₁ (hψ₁ i) (t i)))) :
    LB.Gen.Maps (LB.linCombIso w φ₂ ε) t₂
      (GeneratorPullback.boxGen M pr φ₂ ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ₂ i) (φ i) ε φ₂ (hψ₂ i) (t i))) := by sorry
