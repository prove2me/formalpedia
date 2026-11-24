-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_Packing_exists_max_sep
-- name    : GlobalTheory.CompanionTheory.Adelic.Packing.exists_max_sep
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:16:07.48444+00:00
-- url     : https://prove2.me/theorems/d90c7bb0-32e0-42b2-a5fd-2376a54d6154
-- title:
--   Packing: exists max sep
-- statement:
--   The Packing construction uses the exists max sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeBallCountRatioBound.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeBallCountRatioBound.lean#L40-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.Packing
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Λ : Type} [AddCommGroup Λ]

theorem GlobalTheory.CompanionTheory.Adelic.Packing.exists_max_sep (e : Λ →+ V) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∃ s : Finset Λ, Sep e r R s ∧ ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card := by sorry
