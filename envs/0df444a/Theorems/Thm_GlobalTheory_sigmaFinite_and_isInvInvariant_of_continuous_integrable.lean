-- Prove2me | Theorems.Thm_GlobalTheory_sigmaFinite_and_isInvInvariant_of_continuous_integrable
-- name    : GlobalTheory.sigmaFinite_and_isInvInvariant_of_continuous_integrable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:17.435086+00:00
-- url     : https://prove2.me/theorems/17fe5ba5-1e8e-4482-808b-c27491586567
-- title:
--   Global Theory: sigma Finite and is Inv Invariant of continuous integrable
-- statement:
--   The Global Theory construction uses the sigma Finite and is Inv Invariant of continuous integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SigmaFiniteAndIsInvInvariantOfContinuousIntegrab.lean#L8-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SigmaFiniteAndIsInvInvariantOfContinuousIntegrab.lean#L8-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SigmaFiniteAndIsInvInvariantOfContinuousIntegrab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.sigmaFinite_and_isInvInvariant_of_continuous_integrable :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
      [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : G → ℂ),
      Continuous f → f 1 ≠ 0 → Integrable f μ → SigmaFinite μ ∧ μ.IsInvInvariant := by sorry
