-- Prove2me | Theorems.Thm_MainStatements_Hodge_Pf_AXO_sep_tensor
-- name    : MainStatements.Hodge.Pf.AXO.sep_tensor
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:04:44.987181+00:00
-- url     : https://prove2.me/theorems/eb9eee28-86c2-58e3-a346-029299227f6c
-- title:
--   AXO: sep tensor
-- statement:
--   The AXO construction uses the sep tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianPullbackLattices/GeoSys.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianPullbackLattices/GeoSys.lean#L19-L21

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianSchemeCharts_FinSys
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianSchemeCharts_IsOpenImmersionProdChart
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_GeoSys
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.AXO
variable {R : Type} [CommRing R]

theorem MainStatements.Hodge.Pf.AXO.sep_tensor (A : Over (Sp R)) [IsSeparated A.hom] : IsSeparated (A ⊗ A).hom := by sorry
