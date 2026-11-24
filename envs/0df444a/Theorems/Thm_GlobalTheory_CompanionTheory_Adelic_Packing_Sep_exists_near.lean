-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_Packing_Sep_exists_near
-- name    : GlobalTheory.CompanionTheory.Adelic.Packing.Sep.exists_near
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:16:06.495205+00:00
-- url     : https://prove2.me/theorems/1be04a15-0403-4331-84da-e5492849c4ce
-- title:
--   Sep: exists near
-- statement:
--   The Sep construction uses the exists near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeBallCountRatioBound.lean#L51-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeBallCountRatioBound.lean#L51-L75

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

theorem GlobalTheory.CompanionTheory.Adelic.Packing.Sep.exists_near {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) {s : Finset Λ}
    (hs : Sep e r R s) (hmax : ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card)
    {l : Λ} (hl : ‖e l‖ ≤ R) : ∃ t ∈ s, ‖e (l - t)‖ ≤ r := by sorry
