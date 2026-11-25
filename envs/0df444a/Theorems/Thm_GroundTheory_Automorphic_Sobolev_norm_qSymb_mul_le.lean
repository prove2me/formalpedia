-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_qSymb_mul_le
-- name    : GroundTheory.Automorphic.Sobolev.norm_qSymb_mul_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:14.692261+00:00
-- url     : https://prove2.me/theorems/6c0343a7-dcd8-4ee2-b4a4-3fb9db7d0c90
-- title:
--   Sobolev: norm q Symb mul le
-- statement:
--   The Sobolev construction uses the norm q Symb mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L123-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L123-L129

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

theorem GroundTheory.Automorphic.Sobolev.norm_qSymb_mul_le {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    ‖qSymb c w μ ξ‖ * ‖symb0 c w ξ‖ ≤ 1 := by sorry
