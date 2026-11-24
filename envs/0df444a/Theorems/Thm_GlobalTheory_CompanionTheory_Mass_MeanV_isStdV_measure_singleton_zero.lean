-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_isStdV_measure_singleton_zero
-- name    : GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:53:56.012431+00:00
-- url     : https://prove2.me/theorems/11f3f5bb-2520-424c-a158-eb1fde9c0c2f
-- title:
--   Mean V: is Std V measure singleton zero
-- statement:
--   The Mean V construction uses the is Std V measure singleton zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalHaarMeasureSingleton.lean#L9-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalHaarMeasureSingleton.lean#L9-L38

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalHaarMeasureSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV

theorem GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)), IsStdV v lam → lam {0} = 0 := by sorry
