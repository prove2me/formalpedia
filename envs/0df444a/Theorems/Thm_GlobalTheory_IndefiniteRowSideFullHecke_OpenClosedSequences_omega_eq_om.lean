-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenClosedSequences_omega_eq_om
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omega_eq_om
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:20.935204+00:00
-- url     : https://prove2.me/theorems/3ede9ca7-671c-4488-9b5b-e7bba9f2307a
-- title:
--   Open Closed Sequences: omega eq om
-- statement:
--   The Open Closed Sequences construction uses the omega eq om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/OpenClosedSequences.lean#L111-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/OpenClosedSequences.lean#L111-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable (a b)
variable {a b}

theorem GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omega_eq_om (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (Φ : SB (Matrix b a k)) :
    (omega a b μ (g, h) Φ).1 = om μ⁻¹ g h Φ.1 := by sorry
