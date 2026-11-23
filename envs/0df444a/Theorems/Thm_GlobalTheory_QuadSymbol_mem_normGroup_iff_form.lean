-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_mem_normGroup_iff_form
-- name    : GlobalTheory.QuadSymbol.mem_normGroup_iff_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:11.85898+00:00
-- url     : https://prove2.me/theorems/93355c6e-5f39-4a74-9d55-cf024cda2701
-- title:
--   Quad Symbol: mem norm Group iff form
-- statement:
--   The Quad Symbol construction uses the mem norm Group iff form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L141-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L141-L169

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

theorem GlobalTheory.QuadSymbol.mem_normGroup_iff_form (e : Module.Basis (Fin 2) K L)
    (h0 : e 0 = 1) {δ : K} (h1 : e 1 * e 1 = algebraMap K L δ) {A : Type} [CommRing A]
    [Algebra K A] {x : Aˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K L A ↔
      ∃ a b : A, (x : A) = a ^ 2 - algebraMap K A δ * b ^ 2 := by sorry
