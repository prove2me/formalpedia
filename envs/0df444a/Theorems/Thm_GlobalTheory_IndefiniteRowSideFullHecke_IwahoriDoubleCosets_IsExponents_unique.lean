-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_IwahoriDoubleCosets_IsExponents_unique
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsExponents.unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:14:29.108835+00:00
-- url     : https://prove2.me/theorems/9a34ba9b-fb1e-4c60-bf72-7e75f810579d
-- title:
--   Is Exponents: unique
-- statement:
--   The Is Exponents construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IwahoriDoubleCosets.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IwahoriDoubleCosets.lean#L81-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BorelCasselman
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
variable {k n}
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsExponents.unique {π : Representation ℂ (GL n k) V} {E E' : Multiset ((n → kˣ) →* ℂˣ)}
    (h : IsExponents π E) (h' : IsExponents π E') : E = E' := by sorry
