-- Prove2me | Theorems.Thm_GlobalTheory_PowAlongIso_sq_iff
-- name    : GlobalTheory.PowAlongIso.sq_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:19:35.491235+00:00
-- url     : https://prove2.me/theorems/4b680bfa-6cdf-4928-beb9-42eb10b573df
-- title:
--   Pow Along Iso: sq iff
-- statement:
--   The Pow Along Iso construction uses the sq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L253-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L253-L298

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
variable {B B' X X' X'' T T' T'' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB X} {L' : LB X'} {L'' : LB X''} {j : ℕ}
  {prB : Fin j → (B' ⟶ B)} {pr : Fin j → (X' ⟶ X)} {p : T ⟶ B} {f : T ⟶ X} {p' : T' ⟶ B'} {f' : T' ⟶ X'}

theorem GlobalTheory.PowAlongIso.sq_iff (wD : LB.Iso M' (LB.LinComb M prB (fun _ => 1))) (wL : LB.Iso L' (LB.LinComb L pr (fun _ => 1)))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) (ρ : Fin j → (T' ⟶ T)) :
    Sq wD wL w w' ρ ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jNM : Fin j → M.ι) (jM' : M'.ι) (jL' : L'.ι)
      (jNL : Fin j → L.ι), p' (r z) ∈ LB.wchart M prB jNM → p' (r z) ∈ M'.U jM' → f' (r z) ∈ L'.U jL' →
      (∀ i, p (ρ i (r z)) ∈ M.U (jNM i)) → (∀ i, f (ρ i (r z)) ∈ L.U (jNL i)) → f' (r z) ∈ LB.wchart L pr jNL →
      bw wD (r ≫ p') z jNM jM' * gw w' r z jM' (fun _ => jL') =
        (∏ i, gw w (r ≫ ρ i) z (jNM i) (fun _ => jNL i)) * bw wL (r ≫ f') z jNL jL' := by sorry
