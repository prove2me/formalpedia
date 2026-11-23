-- Prove2me | Theorems.Thm_GlobalTheory_polyChartHom_C
-- name    : GlobalTheory.polyChartHom_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:26.177471+00:00
-- url     : https://prove2.me/theorems/2049d156-859d-4112-b7d7-30dda4edffd1
-- title:
--   Global Theory: poly Chart Hom C
-- statement:
--   The Global Theory construction uses the poly Chart Hom C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PolyChartSmoothFractionLift.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PolyChartSmoothFractionLift.lean#L26-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_PolyChartSmoothFractionLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
variable {K F₀ : Type} (V : Type) [Field K] [Field F₀] [Algebra K F₀] (R₀ : Subalgebra K F₀)

theorem GlobalTheory.polyChartHom_C (a : R₀) :
    polyChartHom V R₀ (C a) = algebraMap F₀ (FractionRing (MvPolynomial V F₀)) a := by sorry
