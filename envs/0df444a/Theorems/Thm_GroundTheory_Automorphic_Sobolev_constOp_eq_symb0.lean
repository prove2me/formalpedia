-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_constOp_eq_symb0
-- name    : GroundTheory.Automorphic.Sobolev.constOp_eq_symb0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:17.098087+00:00
-- url     : https://prove2.me/theorems/3cd721f8-d5ed-5750-9422-d681d31a3e6e
-- title:
--   Sobolev: const Op eq symb0
-- statement:
--   The Sobolev construction uses the const Op eq symb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L46-L47

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
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
variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E)

theorem GroundTheory.Automorphic.Sobolev.constOp_eq_symb0 : constOp w c = fourierMultiplierCLM ℂ (symb0 c w) := by sorry
