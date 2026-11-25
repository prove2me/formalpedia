-- Prove2me | Theorems.Thm_GlobalTheory_PowAlongIso_isGen_germ
-- name    : GlobalTheory.PowAlongIso.isGen_germ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:19:42.489531+00:00
-- url     : https://prove2.me/theorems/b76ec4b0-7625-47af-8f36-6bd5dc9c3fa7
-- title:
--   Pow Along Iso: is Gen germ
-- statement:
--   The Pow Along Iso construction uses the is Gen germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L22-L36

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

theorem GlobalTheory.PowAlongIso.isGen_germ {L' L : LB X} (w : LB.Iso L' L) : w.IsGen ↔ ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (j j' : L.ι)
    (k k' : L'.ι), f y ∈ L.U j → f y ∈ L.U j' → f y ∈ L'.U k → f y ∈ L'.U k' →
    gm f y (L.U j ⊓ L'.U k) (w.s (j, k)) =
      gm f y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gm f y (L.U j' ⊓ L'.U k') (w.s (j', k')) := by sorry
