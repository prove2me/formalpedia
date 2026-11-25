-- Prove2me | Theorems.Thm_GlobalTheory_PowAlongIso_exists_mapsAt
-- name    : GlobalTheory.PowAlongIso.exists_mapsAt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:27:45.87116+00:00
-- url     : https://prove2.me/theorems/d932358f-0464-5a7d-bc44-22936bf8d46b
-- title:
--   Pow Along Iso: exists maps At
-- statement:
--   The Pow Along Iso construction uses the exists maps At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L200-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L200-L229

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

theorem GlobalTheory.PowAlongIso.exists_mapsAt (hM' : M'.IsLB) {E : X'' ⟶ X'} {pr' : Fin j → (X'' ⟶ X)} (hpr : ∀ i, pr' i = E ≫ pr i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {w' : LB.Iso M'' (M'.pull E)}
    {w'' : LB.Iso M'' (LB.LinComb M pr' (fun _ => 1))}
    (T : ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z)
      (a : Fin j → M.ι) (b : M'.ι) (c : M''.ι), f z ∈ LB.wchart M pr' a → E (f z) ∈ M'.U b → f z ∈ M''.U c →
      bw w'' f z a c = bw w (f ≫ E) z a b * gw w' f z b c)
    {p : Y ⟶ X'} {p' : Y ⟶ X''} (hp : p' ≫ E = p) {a : LB.Gen (M'.pull p)} {a' : LB.Gen (M''.pull p')}
    (H : PMaps w' (K := PUnit) (fun _ => p') (fun _ => p) (fun _ => 1) a' a (𝟙 _))
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb M φ ε))
    (h : ∃ b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p ≫ pr i) (fun _ => 1)),
      GeneratorPullback.MapsAt M M' pr w p 1 a b ∧ LB.Gen.Corr M _ _ _ _ b c) :
    ∃ b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p' ≫ pr' i) (fun _ => 1)),
      GeneratorPullback.MapsAt M M'' pr' w'' p' 1 a' b ∧ LB.Gen.Corr M _ _ _ _ b c := by sorry
