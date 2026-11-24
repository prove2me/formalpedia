-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGen_const_of_isIntegral
-- name    : GlobalTheory.ThetaGen.const_of_isIntegral
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:06:10.832445+00:00
-- url     : https://prove2.me/theorems/2f936268-5a71-4e89-8d49-8b9bc5d88650
-- title:
--   Theta Gen: const of is Integral
-- statement:
--   The Theta Gen construction uses the const of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsHomogeneousOfMemSpanPow.lean#L214-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsHomogeneousOfMemSpanPow.lean#L214-L238

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.ThetaGen.const_of_isIntegral {ι : Type} (θ : ι → E → ℂ) {f : E → ℂ} (hf : Differentiable ℂ f)
    (hint : IsIntegral (Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2))
      (fun p : ℂ × E => p.1 ^ 0 * f p.2)) (z : E) : f z = f 0 := by sorry
