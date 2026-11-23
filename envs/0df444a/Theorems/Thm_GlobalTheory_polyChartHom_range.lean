-- Prove2me | Theorems.Thm_GlobalTheory_polyChartHom_range
-- name    : GlobalTheory.polyChartHom_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:34.3918+00:00
-- url     : https://prove2.me/theorems/5967fcfa-44d4-4e11-8044-f8082b0c748a
-- title:
--   Global Theory: poly Chart Hom range
-- statement:
--   The Global Theory construction uses the poly Chart Hom range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PolyChartSmoothFractionLift.lean#L37-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/PolyChartSmoothFractionLift.lean#L37-L56

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

theorem GlobalTheory.polyChartHom_range :
    (polyChartHom V R₀).range = Algebra.adjoin K
      ((algebraMap F₀ (FractionRing (MvPolynomial V F₀))) '' (R₀ : Set F₀) ∪
        Set.range fun v : V =>
          algebraMap (MvPolynomial V F₀) (FractionRing (MvPolynomial V F₀)) (X v)) := by sorry
