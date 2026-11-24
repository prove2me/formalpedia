-- Prove2me | Theorems.Thm_GlobalTheory_SympTower_rank_le_of_smul_sub_eq_zero
-- name    : GlobalTheory.SympTower.rank_le_of_smul_sub_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:25:00.820857+00:00
-- url     : https://prove2.me/theorems/f1904e7c-cc6f-472f-bc31-1e9202a9a890
-- title:
--   Symp Tower: rank le of smul sub eq zero
-- statement:
--   The Symp Tower construction uses the rank le of smul sub eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompatibleSymplectic.lean#L6-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompatibleSymplectic.lean#L6-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompatibleSymplectic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SympTower

theorem GlobalTheory.SympTower.rank_le_of_smul_sub_eq_zero {R : Type} [CommRing R] [Finite R] {r : ℕ} {ι : Type}
    [Fintype ι] (φ : (ι → R) →ₗ[R] (Fin r → R)) (ψ : (Fin r → R) →ₗ[R] (ι → R)) (c : R)
    (hc : c ≠ 0) (h : ∀ x, c • (x - φ (ψ x)) = 0) : r ≤ Fintype.card ι := by sorry
