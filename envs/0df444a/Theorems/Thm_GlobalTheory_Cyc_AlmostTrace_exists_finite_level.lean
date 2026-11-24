-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_exists_finite_level
-- name    : GlobalTheory.Cyc.AlmostTrace.exists_finite_level
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:32:35.118748+00:00
-- url     : https://prove2.me/theorems/aef18d3d-724c-47c4-aa29-e1748d455128
-- title:
--   Almost Trace: exists finite level
-- statement:
--   The Almost Trace construction uses the exists finite level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceAlmostOntoOfLevels.lean#L111-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceAlmostOntoOfLevels.lean#L111-L163

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.AlmostTrace
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.AlmostTrace.exists_finite_level (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) :
    ∃ L' : FinExt l, L'.1 ≤ L ∧ ∃ i₀, ∀ i ≥ i₀, ∀ h ∈ Gj K i,
      ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup := by sorry
