-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_UnipHaar_map_preimage_conj
-- name    : GlobalTheory.SmGL.UnipHaar.map_preimage_conj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:14:07.533497+00:00
-- url     : https://prove2.me/theorems/d4a99790-358d-4b3a-910e-0690395c7c8e
-- title:
--   Unip Haar: map preimage conj
-- statement:
--   The Unip Haar construction uses the map preimage conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L275-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularOneAddMat.lean#L275-L290

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem GlobalTheory.SmGL.UnipHaar.map_preimage_conj (g : Levi k m) {T : Set (unipRad k e)} (hT : MeasurableSet T) :
    Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν) T = ENNReal.ofReal (modulus k m g) *
      Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν) (conj e g ⁻¹' T) := by sorry
