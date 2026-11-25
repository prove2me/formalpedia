-- Prove2me | Theorems.Thm_GlobalTheory_St_HaarSplit_exists_haar_map_prod_eq
-- name    : GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:46.95921+00:00
-- url     : https://prove2.me/theorems/07748a90-1f7c-45ba-8293-00f2abca7602
-- title:
--   Haar Split: exists haar map prod eq
-- statement:
--   The Haar Split construction uses the exists haar map prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHaarMapProdEq.lean#L8-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsHaarMapProdEq.lean#L8-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHaarMapProdEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure
open scoped NNReal ENNReal
open GlobalTheory GlobalTheory.St GlobalTheory.St.HaarSplit

theorem GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [BorelSpace A] [BorelSpace B] [BorelSpace C]
    [LocallyCompactSpace A] [LocallyCompactSpace B] [LocallyCompactSpace C]
    [SecondCountableTopology A] [SecondCountableTopology B] [SecondCountableTopology C]
    (e : (A × B) ≃ₜ* C) (μA : Measure A) [μA.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure] :
    ∃ μB : Measure B, μB.IsHaarMeasure ∧ (μA.prod μB).map e = μC := by sorry
