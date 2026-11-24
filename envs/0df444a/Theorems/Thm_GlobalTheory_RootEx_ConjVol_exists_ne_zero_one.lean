-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ConjVol_exists_ne_zero_one
-- name    : GlobalTheory.RootEx.ConjVol.exists_ne_zero_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:28.808194+00:00
-- url     : https://prove2.me/theorems/e92d1ff4-3212-43f6-ae6d-bddc8681d284
-- title:
--   Conj Vol: exists ne zero one
-- statement:
--   The Conj Vol construction uses the exists ne zero one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L120-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ConjVol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RootEx.ConjVol.exists_ne_zero_one [ValuativeRel.IsNontrivial k] : ∃ a : k, a ≠ 0 ∧ a ≠ 1 := by sorry
