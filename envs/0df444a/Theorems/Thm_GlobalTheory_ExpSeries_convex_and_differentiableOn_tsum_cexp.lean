-- Prove2me | Theorems.Thm_GlobalTheory_ExpSeries_convex_and_differentiableOn_tsum_cexp
-- name    : GlobalTheory.ExpSeries.convex_and_differentiableOn_tsum_cexp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:53.257723+00:00
-- url     : https://prove2.me/theorems/c71cb399-f405-4760-a5f4-575d16e52d1d
-- title:
--   Exp Series: convex and differentiable On tsum cexp
-- statement:
--   The Exp Series construction uses the convex and differentiable On tsum cexp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConvexAndDifferentiableOnTsumCexp.lean#L20-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConvexAndDifferentiableOnTsumCexp.lean#L20-L53

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

theorem GlobalTheory.ExpSeries.convex_and_differentiableOn_tsum_cexp :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (J : Type)
      (c : J → ℂ) (L : J → V →ₗ[ℂ] ℂ),
      Convex ℝ {z : V | Summable fun j => c j * cexp (L j z)} ∧
      DifferentiableOn ℂ (fun z : V => ∑' j, c j * cexp (L j z))
        (interior {z : V | Summable fun j => c j * cexp (L j z)}) := by sorry
