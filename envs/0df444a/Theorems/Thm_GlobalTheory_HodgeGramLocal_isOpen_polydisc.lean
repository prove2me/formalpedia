-- Prove2me | Theorems.Thm_GlobalTheory_HodgeGramLocal_isOpen_polydisc
-- name    : GlobalTheory.HodgeGramLocal.isOpen_polydisc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:11.002746+00:00
-- url     : https://prove2.me/theorems/51eeefb8-ee5e-4160-a740-f6ea4e16b7d5
-- title:
--   Hodge Gram Local: is Open polydisc
-- statement:
--   The Hodge Gram Local construction uses the is Open polydisc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L62-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeGramLocal
variable {n a g : ℕ}

theorem GlobalTheory.HodgeGramLocal.isOpen_polydisc (n : ℕ) : IsOpen (polydisc n 1) := by sorry
