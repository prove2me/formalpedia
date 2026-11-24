-- Prove2me | Theorems.Thm_GlobalTheory_JR_EtQuot_exists_idem
-- name    : GlobalTheory.JR.EtQuot.exists_idem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:31:14.836605+00:00
-- url     : https://prove2.me/theorems/ce33892f-dada-4da4-968e-d5218b6b733e
-- title:
--   Et Quot: exists idem
-- statement:
--   The Et Quot construction uses the exists idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleInvolutiveAlgebraSplittingSmaller.lean#L119-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleInvolutiveAlgebraSplittingSmaller.lean#L119-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmaller
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtQuot
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable (A : Et F E) (e : A.K)

theorem GlobalTheory.JR.EtQuot.exists_idem (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] [Nontrivial K] (hf : ¬ IsField K) :
    ∃ e : K, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by sorry
