-- Prove2me | Theorems.Thm_GlobalTheory_PowAlongIso_main
-- name    : GlobalTheory.PowAlongIso.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:30:11.319959+00:00
-- url     : https://prove2.me/theorems/9fdab9f6-3053-5c66-8705-1ad4902a5d19
-- title:
--   Pow Along Iso: main
-- statement:
--   The Pow Along Iso construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L329-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean#L329-L355

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

theorem GlobalTheory.PowAlongIso.main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G) (U : Unif I D A G) (U' : Unif I D A G'), IsMonHom ε.hom → SameUnif ε U.toUnifPre U'.toUnifPre → ∀ (j : ℕ) (D₀ : DegData R I) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif I D₀ A₀ G₀) (pD : IsPowDeg D.toPre D₀.toPre j) (pA : IsPowPolAV A A₀ j) (pG : IsPowGrp G G₀ j) (pG' : IsPowGrp G' G₀ j), (∀ i, ε.hom ≫ pG.pr i = pG'.pr i) → Nonempty (UnifPowOf3 pD pA pG U U₀) → Nonempty (UnifPowOf3 pD pA pG' U' U₀) := by sorry
