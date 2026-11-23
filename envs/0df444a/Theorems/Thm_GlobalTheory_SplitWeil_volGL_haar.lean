-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_volGL_haar
-- name    : GlobalTheory.SplitWeil.volGL_haar
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:50.015157+00:00
-- url     : https://prove2.me/theorems/ce284ed2-7b01-44de-bc6e-cf73a685a19a
-- title:
--   Split Weil: vol GL haar
-- statement:
--   The Split Weil construction uses the vol GL haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsMulLeftInvariantVolGL.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsMulLeftInvariantVolGL.lean#L151-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem GlobalTheory.SplitWeil.volGL_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure], BorelSpace (GL n k) ∧ LocallyCompactSpace (GL n k) ∧ SecondCountableTopology (GL n k) ∧ IsCompact (KO k n : Set (GL n k)) ∧ IsOpen (KO k n : Set (GL n k)) ∧ IsOpen (KOne k n : Set (GL n k)) ∧ (volGL ν n).IsHaarMeasure ∧ (volGL ν n).IsMulRightInvariant := by sorry
