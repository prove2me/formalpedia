-- Prove2me | Theorems.Thm_GlobalTheory_LatL_glO_transitive_pairs
-- name    : GlobalTheory.LatL.glO_transitive_pairs
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:26.28825+00:00
-- url     : https://prove2.me/theorems/399e5e90-1fb7-4377-b0e1-e941101e444d
-- title:
--   Lat L: gl O transitive pairs
-- statement:
--   The Lat L construction uses the gl O transitive pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormSubLeMaxUltra.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormSubLeMaxUltra.lean#L94-L100

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

theorem GlobalTheory.LatL.glO_transitive_pairs : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (v w : Fin (r + 1) → F), (∀ i, ‖v i‖ ≤ 1) →
    (∀ i, ‖w i‖ ≤ 1) → w ⬝ᵥ v = 1 → ∃ k ∈ glO (r + 1) F,
      (k : Matrix _ _ F) *ᵥ Pi.single (Fin.last r) 1 = v ∧ w ᵥ* (k : Matrix _ _ F) = Pi.single (Fin.last r) 1 := by sorry
