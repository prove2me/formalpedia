-- Prove2me | Theorems.Thm_GlobalTheory_IwasawaShape_lintegral_mul_left_of_map
-- name    : GlobalTheory.IwasawaShape.lintegral_mul_left_of_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:55.326959+00:00
-- url     : https://prove2.me/theorems/ed62f073-bd1f-4ef5-90d7-5cadf73fbf0e
-- title:
--   Iwasawa Shape: lintegral mul left of map
-- statement:
--   The Iwasawa Shape construction uses the lintegral mul left of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMapMulRightEqSmul.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMapMulRightEqSmul.lean#L10-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMapMulRightEqSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.IwasawaShape
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
omit [MeasurableInv G]

theorem GlobalTheory.IwasawaShape.lintegral_mul_left_of_map {ρ : Measure G} {p : G} (h : ρ.map (fun g => p * g) = ρ) (f : G → ENNReal)
    (hf : Measurable f) : ∫⁻ x, f (p * x) ∂ρ = ∫⁻ x, f x ∂ρ := by sorry
