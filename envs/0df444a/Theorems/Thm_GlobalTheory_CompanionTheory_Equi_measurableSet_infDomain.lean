-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_measurableSet_infDomain
-- name    : GlobalTheory.CompanionTheory.Equi.measurableSet_infDomain
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:37:56.718003+00:00
-- url     : https://prove2.me/theorems/22800f7b-9c61-492c-b26b-ec90918d1667
-- title:
--   Equi: measurable Set inf Domain
-- statement:
--   The Equi construction uses the measurable Set inf Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanFundamentalDomainIntegers.lean#L35-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanFundamentalDomainIntegers.lean#L35-L35

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegers
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi
open GlobalTheory.CompanionTheory.SW.RealCoord
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem GlobalTheory.CompanionTheory.Equi.measurableSet_infDomain : MeasurableSet (infDomain F) := by sorry
