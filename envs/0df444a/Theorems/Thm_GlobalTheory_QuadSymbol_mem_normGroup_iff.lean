-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_mem_normGroup_iff
-- name    : GlobalTheory.QuadSymbol.mem_normGroup_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:26.719818+00:00
-- url     : https://prove2.me/theorems/a1fd42b2-a63d-46f9-9395-61876921fd8c
-- title:
--   Quad Symbol: mem norm Group iff
-- statement:
--   The Quad Symbol construction uses the mem norm Group iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L70-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.QuadSymbol
variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable {K L}
open NumberField IsDedekindDomain
open scoped TensorProduct
variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable {K L}

theorem GlobalTheory.QuadSymbol.mem_normGroup_iff [FiniteDimensional K L] {A : Type} [CommRing A]
    [Algebra K A] {x : Aˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K L A ↔ ∃ z : A ⊗[K] L, Algebra.norm A z = x := by sorry
