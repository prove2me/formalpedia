-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomologyUniversal_lid_lTensor_apply
-- name    : GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal.lid_lTensor_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:26:58.860961+00:00
-- url     : https://prove2.me/theorems/baa0ddd0-c4c0-43b0-812e-1ac9ae706cbc
-- title:
--   Perfect First Cohomology Universal: lid l Tensor apply
-- statement:
--   The Perfect First Cohomology Universal construction uses the lid l Tensor apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuasiIsomorphismDegreeOneKernel.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuasiIsomorphismDegreeOneKernel.lean#L7-L13

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuasiIsomorphismDegreeOneKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal

theorem GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal.lid_lTensor_apply {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) (u : R ⊗[R] X) :
    TensorProduct.lid R Y (f.lTensor R u) = f (TensorProduct.lid R X u) := by sorry
