-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeOf_of_low
-- name    : GlobalTheory.CompanionTheory.WedgeOf.wedgeOf_of_low
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:52.502659+00:00
-- url     : https://prove2.me/theorems/aca0e757-1f2b-473c-b173-3082b49d78df
-- title:
--   Wedge Of: wedge Of of low
-- statement:
--   The Wedge Of construction uses the wedge Of of low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeTSurjective.lean#L30-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeTSurjective.lean#L30-L70

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CupVanishingAntisymmetricCrossStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjectiveStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorSquareVectorBundleRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BijectiveOfSurjectiveSameRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeTSurjective
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf

theorem GlobalTheory.CompanionTheory.WedgeOf.wedgeOf_of_low : LowSt → WedgeOfSt := by sorry
