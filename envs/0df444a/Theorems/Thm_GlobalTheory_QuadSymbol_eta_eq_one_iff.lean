-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_one_iff
-- name    : GlobalTheory.QuadSymbol.eta_eq_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:07.013831+00:00
-- url     : https://prove2.me/theorems/f20fa706-8bcd-4fb8-aade-5c04ef3aa284
-- title:
--   Quad Symbol: eta eq one iff
-- statement:
--   The Quad Symbol construction uses the eta eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L33-L39

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

theorem GlobalTheory.QuadSymbol.eta_eq_one_iff {A : Type} [CommRing A] [Algebra K A] {x : Aˣ} :
    _root_.GlobalTheory.QuadSymbol.eta K L A x = 1 ↔ x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K L A := by sorry
