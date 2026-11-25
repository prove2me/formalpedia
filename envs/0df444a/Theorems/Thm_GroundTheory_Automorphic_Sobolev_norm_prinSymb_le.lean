-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_prinSymb_le
-- name    : GroundTheory.Automorphic.Sobolev.norm_prinSymb_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:14:30.527372+00:00
-- url     : https://prove2.me/theorems/d8d672d0-f8e3-4193-86aa-fb690aa65387
-- title:
--   Sobolev: norm prin Symb le
-- statement:
--   The Sobolev construction uses the norm prin Symb le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L350-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L350-L357

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GroundTheory.Automorphic.Sobolev.norm_prinSymb_le {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) (ξ : E) :
    ‖prinSymb c w ξ‖ ≤ (∑ i, ‖c i‖ * ∏ j, ‖w i j‖) * ‖ξ‖ ^ m := by sorry
