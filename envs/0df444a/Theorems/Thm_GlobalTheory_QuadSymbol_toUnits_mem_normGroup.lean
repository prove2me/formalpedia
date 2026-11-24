-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_toUnits_mem_normGroup
-- name    : GlobalTheory.QuadSymbol.toUnits_mem_normGroup
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:53:27.088025+00:00
-- url     : https://prove2.me/theorems/8c2b0422-96a2-4f4c-b21f-23f16c46cd57
-- title:
--   Quad Symbol: to Units mem norm Group
-- statement:
--   The Quad Symbol construction uses the to Units mem norm Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L110-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L110-L116

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

theorem GlobalTheory.QuadSymbol.toUnits_mem_normGroup [FiniteDimensional K L] (A : Type) [CommRing A]
    [Algebra K A] {x : Kˣ} (hx : x ∈ _root_.GlobalTheory.QuadSymbol.globalNorms K L) :
    _root_.GlobalTheory.QuadSymbol.toUnits K A x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K L A := by sorry
