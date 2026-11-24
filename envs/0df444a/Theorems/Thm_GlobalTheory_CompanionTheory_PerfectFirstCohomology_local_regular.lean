-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_local_regular
-- name    : GlobalTheory.CompanionTheory.PerfectFirstCohomology.local_regular
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:01:45.200788+00:00
-- url     : https://prove2.me/theorems/aa97c6b2-897d-4314-bc06-aeda7d340f5e
-- title:
--   Perfect First Cohomology: local regular
-- statement:
--   The Perfect First Cohomology construction uses the local regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PerfectFirstCohomologyBaseChange.lean#L55-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PerfectFirstCohomologyBaseChange.lean#L55-L83

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatQuotientOfUniversallyInjectiveStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LinearMapZeroOfInjectiveFullRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFreeKernelSplittingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalSplittingKernelBaseChangeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelFreeAtPrimesOfConstantRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelBaseChangeTowerEquivStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RetractBaseChangeKernelCompatibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuasiIsomorphismDegreeOneKernelStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CochainBaseChangeEquivalencesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniversalCoefficientDegreeZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelEquivCohomologyOfQuasiIsomorphismStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyBaseChangeOfCochainEquivsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PerfectFirstCohomologyBaseChange
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfectFirstCohomology

theorem GlobalTheory.CompanionTheory.PerfectFirstCohomology.local_regular (A Q P : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [AddCommGroup P]
    [Module A P] [Module.Finite A Q] [Module.Free A Q] [Module.Finite A P] [Module.Free A P] (d : Q →ₗ[A] P) (g : ℕ)
    (h1 : Module.Free A (LinearMap.ker d)) (h2 : Module.Finite A (LinearMap.ker d))
    (h3 : Module.finrank A (LinearMap.ker d) = g)
    (h4 : Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) = g) :
    ∃ r : P →ₗ[A] Q, d ∘ₗ r ∘ₗ d = d := by sorry
