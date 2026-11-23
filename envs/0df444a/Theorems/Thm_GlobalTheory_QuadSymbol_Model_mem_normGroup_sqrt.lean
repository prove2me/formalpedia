-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Model_mem_normGroup_sqrt
-- name    : GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:14.48379+00:00
-- url     : https://prove2.me/theorems/44d5f26a-3152-40e8-91f5-2f0ed4f7856c
-- title:
--   Model: mem norm Group sqrt
-- statement:
--   The Model construction uses the mem norm Group sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L30-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
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
open GlobalTheory.QuadSymbol
open GlobalTheory GlobalTheory.QuadSymbol GlobalTheory.QuadSymbol.Model
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]
open NumberField IsDedekindDomain
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]

theorem GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt {A : Type} [CommRing A] [Algebra K A] {x : Aˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K (QuadraticAlgebra K d 0) A ↔
      ∃ a b : A, (x : A) = a ^ 2 - algebraMap K A d * b ^ 2 := by sorry
