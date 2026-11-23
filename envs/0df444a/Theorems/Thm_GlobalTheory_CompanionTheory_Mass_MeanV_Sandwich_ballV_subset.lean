-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_Sandwich_ballV_subset
-- name    : GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.ballV_subset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:31.903084+00:00
-- url     : https://prove2.me/theorems/419f665a-dc40-475a-82e5-58ad49e7e2be
-- title:
--   Sandwich: ball V subset
-- statement:
--   The Sandwich construction uses the ball V subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFactorSandwichApprox.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFactorSandwichApprox.lean#L28-L35

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirVolumeRatios_AdeleLC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorSandwichApprox
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.ballV_subset (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ballV v n ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := by sorry
