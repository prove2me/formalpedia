-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Model_eta_real_place
-- name    : GlobalTheory.QuadSymbol.Model.eta_real_place
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:22.979722+00:00
-- url     : https://prove2.me/theorems/ce0d49fb-47ac-43c9-a275-dda16b275041
-- title:
--   Model: eta real place
-- statement:
--   The Model construction uses the eta real place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L53-L64

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
variable {K : Type} [Field K] [Fact (∀ r : K, r ^ 2 ≠ -1 + 0 * r)]
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [Fact (∀ r : K, r ^ 2 ≠ -1 + 0 * r)]

theorem GlobalTheory.QuadSymbol.Model.eta_real_place (w : InfinitePlace K) (hw : w.IsReal) :
    _root_.GlobalTheory.QuadSymbol.eta K (QuadraticAlgebra K (-1) 0) w.Completion
      (_root_.GlobalTheory.QuadSymbol.infDiag K (-1) w) = -1 := by sorry
