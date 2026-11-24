-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ConjVol_colE_mem
-- name    : GlobalTheory.RootEx.ConjVol.colE_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:36.415813+00:00
-- url     : https://prove2.me/theorems/c4a3b68e-c46d-4f32-be4d-541ab9ef67ad
-- title:
--   Conj Vol: col E mem
-- statement:
--   The Conj Vol construction uses the col E mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L101-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Theorems.Thm_GlobalTheory_RootEx_Model_colE_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_colE_mem

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
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.RootEx.ConjVol.colE_mem (p : ℕ) (β : n → k) :
    colE c p β ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) := by sorry
