-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_LatSum_card_reps
-- name    : GlobalTheory.CompanionTheory.Equi.LatSum.card_reps
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:00.105631+00:00
-- url     : https://prove2.me/theorems/96d9c4bb-8eb6-4477-a403-5da7dadc5be7
-- title:
--   Lat Sum: card reps
-- statement:
--   The Lat Sum construction uses the card reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeCosetScaledRiemannSum.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeCosetScaledRiemannSum.lean#L21-L30

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScalingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegersStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ScalingMeasureProductArchimedeanStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeCosetScaledRiemannSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.LatSum
variable {A O Q ι : Type} [AddCommGroup A] [AddCommGroup O] [Fintype ι] [Fintype Q]

theorem GlobalTheory.CompanionTheory.Equi.LatSum.card_reps (j : O →+ A) (hj : Function.Injective j) (q : O → Q) (rep : Q → O)
    (hrep : ∀ c, q (rep c) = c) :
    (reps (ι := ι) j rep).card = Fintype.card Q ^ Fintype.card ι := by sorry
