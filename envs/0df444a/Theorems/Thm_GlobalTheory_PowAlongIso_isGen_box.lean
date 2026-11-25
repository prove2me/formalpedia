-- Prove2me | Theorems.Thm_GlobalTheory_PowAlongIso_isGen_box
-- name    : GlobalTheory.PowAlongIso.isGen_box
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:19:36.534849+00:00
-- url     : https://prove2.me/theorems/ed1f7b30-cf0d-4723-ab0c-4a85196b202f
-- title:
--   Pow Along Iso: is Gen box
-- statement:
--   The Pow Along Iso construction uses the is Gen box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L40-L51

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

theorem GlobalTheory.PowAlongIso.isGen_box (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) : w.IsGen ↔ ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X') (z : Z)
    (a a' : Fin j → M.ι) (b b' : M'.ι), ψ z ∈ LB.wchart M pr a → ψ z ∈ LB.wchart M pr a' → ψ z ∈ M'.U b →
    ψ z ∈ M'.U b' →
    bw w ψ z a b = (∏ i, gm (ψ ≫ pr i) z _ (M.g (a i) (a' i))) * (gm ψ z _ (M'.g b b'))⁻¹ * bw w ψ z a' b' := by sorry
