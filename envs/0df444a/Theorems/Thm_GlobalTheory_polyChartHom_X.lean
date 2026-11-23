-- Prove2me | Theorems.Thm_GlobalTheory_polyChartHom_X
-- name    : GlobalTheory.polyChartHom_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:27.686158+00:00
-- url     : https://prove2.me/theorems/01cdf871-6fd9-4235-83be-6ed2552b4a4a
-- title:
--   Global Theory: poly Chart Hom X
-- statement:
--   The Global Theory construction uses the poly Chart Hom X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PolyChartSmoothFractionLift.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PolyChartSmoothFractionLift.lean#L32-L35

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

theorem GlobalTheory.polyChartHom_X (v : V) :
    polyChartHom V R₀ (X v) =
      algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v) := by sorry
