-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_prinSymb_smul
-- name    : GroundTheory.Automorphic.Sobolev.prinSymb_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:14:45.469696+00:00
-- url     : https://prove2.me/theorems/0ed3b280-ce67-4138-a876-e679ac5b686f
-- title:
--   Sobolev: prin Symb smul
-- statement:
--   The Sobolev construction uses the prin Symb smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L339-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L339-L344

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

theorem GroundTheory.Automorphic.Sobolev.prinSymb_smul {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) (t : ℝ)
    (ξ : E) : prinSymb c w (t • ξ) = (t : ℂ) ^ m * prinSymb c w ξ := by sorry
