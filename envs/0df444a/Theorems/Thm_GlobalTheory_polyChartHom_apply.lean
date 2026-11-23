-- Prove2me | Theorems.Thm_GlobalTheory_polyChartHom_apply
-- name    : GlobalTheory.polyChartHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:35.865256+00:00
-- url     : https://prove2.me/theorems/2937faae-d7b1-4b50-ab05-df7822236d98
-- title:
--   Global Theory: poly Chart Hom apply
-- statement:
--   The Global Theory construction uses the poly Chart Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PolyChartSmoothFractionLift.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PolyChartSmoothFractionLift.lean#L16-L18

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

theorem GlobalTheory.polyChartHom_apply (p : MvPolynomial V R₀) :
    polyChartHom V R₀ p = algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀))
      (MvPolynomial.map (R₀.val : R₀ →+* F₀) p) := by sorry
