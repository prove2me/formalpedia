-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_qNSymb_le
-- name    : GroundTheory.Automorphic.Sobolev.norm_qNSymb_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:40.034558+00:00
-- url     : https://prove2.me/theorems/58a2f74b-7e89-5f03-964d-9306032183bc
-- title:
--   Sobolev: norm q NSymb le
-- statement:
--   The Sobolev construction uses the norm q NSymb le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L131-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L131-L139

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

theorem GroundTheory.Automorphic.Sobolev.norm_qNSymb_le {μ : ℝ} (hμ : 0 ≤ μ) (N : ℕ) (ξ : E) :
    ‖qNSymb c w μ N ξ‖ ≤ N * ‖qSymb c w μ ξ‖ := by sorry
