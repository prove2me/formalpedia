-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Model_isQuadratic
-- name    : GlobalTheory.QuadSymbol.Model.isQuadratic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:22.229263+00:00
-- url     : https://prove2.me/theorems/b28e5740-3984-4b20-a3bb-638bf67412f2
-- title:
--   Model: is Quadratic
-- statement:
--   The Model construction uses the is Quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L16-L18

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

theorem GlobalTheory.QuadSymbol.Model.isQuadratic :
    Algebra.IsQuadraticExtension K (QuadraticAlgebra K d 0) := by sorry
