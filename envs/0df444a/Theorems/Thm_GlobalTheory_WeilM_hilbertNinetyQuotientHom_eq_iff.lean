-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_hilbertNinetyQuotientHom_eq_iff
-- name    : GlobalTheory.WeilM.hilbertNinetyQuotientHom_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:49.662992+00:00
-- url     : https://prove2.me/theorems/438cd190-9ed1-462c-89c7-b6bbab61be99
-- title:
--   Weil M: hilbert Ninety Quotient Hom eq iff
-- statement:
--   The Weil M construction uses the hilbert Ninety Quotient Hom eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L195-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L195-L196

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}

theorem GlobalTheory.WeilM.hilbertNinetyQuotientHom_eq_iff {z u : Eˣ} : h90 c z = u ↔ (u : E) * c z = z := by sorry
