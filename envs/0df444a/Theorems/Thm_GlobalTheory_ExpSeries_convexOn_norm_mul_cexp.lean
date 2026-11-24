-- Prove2me | Theorems.Thm_GlobalTheory_ExpSeries_convexOn_norm_mul_cexp
-- name    : GlobalTheory.ExpSeries.convexOn_norm_mul_cexp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:07:42.28027+00:00
-- url     : https://prove2.me/theorems/cd335df9-dfcd-4d5a-a2bf-34d198bddd3a
-- title:
--   Exp Series: convex On norm mul cexp
-- statement:
--   The Exp Series construction uses the convex On norm mul cexp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConvexAndDifferentiableOnTsumCexp.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConvexAndDifferentiableOnTsumCexp.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConvexAndDifferentiableOnTsumCexp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.ExpSeries

theorem GlobalTheory.ExpSeries.convexOn_norm_mul_cexp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (c : ℂ) (L : V →ₗ[ℂ] ℂ) :
    ConvexOn ℝ Set.univ (fun z : V => ‖c * cexp (L z)‖) := by sorry
