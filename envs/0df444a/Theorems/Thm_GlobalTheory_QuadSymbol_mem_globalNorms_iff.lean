-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_mem_globalNorms_iff
-- name    : GlobalTheory.QuadSymbol.mem_globalNorms_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:54.785844+00:00
-- url     : https://prove2.me/theorems/2f19f469-32cd-41fe-812b-25b8c1627351
-- title:
--   Quad Symbol: mem global Norms iff
-- statement:
--   The Quad Symbol construction uses the mem global Norms iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L85-L92

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

theorem GlobalTheory.QuadSymbol.mem_globalNorms_iff [FiniteDimensional K L] {x : Kˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.globalNorms K L ↔ ∃ z : L, Algebra.norm K z = x := by sorry
