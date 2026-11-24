-- Prove2me | Theorems.Thm_GlobalTheory_LatL_exists_glO_pair
-- name    : GlobalTheory.LatL.exists_glO_pair
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:14.867794+00:00
-- url     : https://prove2.me/theorems/1435c8a8-60a7-4de1-b12b-9df36b1f8cee
-- title:
--   Lat L: exists gl O pair
-- statement:
--   The Lat L construction uses the exists gl O pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormSubLeMaxUltra.lean#L11-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormSubLeMaxUltra.lean#L11-L92

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormSubLeMaxUltra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.LatL

theorem GlobalTheory.LatL.exists_glO_pair {F : Type} [NormedField F] [IsUltrametricDist F] (r : ℕ)
    (v w : Fin (r + 1) → F) (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1) (hwv : w ⬝ᵥ v = 1) :
    ∃ k ∈ glO (r + 1) F, (k : Matrix _ _ F) *ᵥ Pi.single (Fin.last r) 1 = v ∧
      w ᵥ* (k : Matrix _ _ F) = Pi.single (Fin.last r) 1 := by sorry
