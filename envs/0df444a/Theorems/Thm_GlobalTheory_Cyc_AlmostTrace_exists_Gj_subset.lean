-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_exists_Gj_subset
-- name    : GlobalTheory.Cyc.AlmostTrace.exists_Gj_subset
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:32:45.255441+00:00
-- url     : https://prove2.me/theorems/5c1a5670-eb86-4d0f-9ee7-87470b2f10c2
-- title:
--   Almost Trace: exists Gj subset
-- statement:
--   The Almost Trace construction uses the exists Gj subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceAlmostOntoOfLevels.lean#L52-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceAlmostOntoOfLevels.lean#L52-L75

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

theorem GlobalTheory.Cyc.AlmostTrace.exists_Gj_subset (K : FinExt l) {U : Set (GQ l)} (hU : IsOpen U)
    (hH : (Hinf K : Set (GQ l)) ⊆ U) : ∃ i₀, ∀ i ≥ i₀, (Gj K i : Set (GQ l)) ⊆ U := by sorry
