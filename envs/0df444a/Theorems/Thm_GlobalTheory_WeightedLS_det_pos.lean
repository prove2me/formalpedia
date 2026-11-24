-- Prove2me | Theorems.Thm_GlobalTheory_WeightedLS_det_pos
-- name    : GlobalTheory.WeightedLS.det_pos
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:52:55.213934+00:00
-- url     : https://prove2.me/theorems/5e1e6b17-6e07-46ea-9a7a-016a740dc037
-- title:
--   Weighted LS: det pos
-- statement:
--   The Weighted LS construction uses the det pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedLeastSquaresBound.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedLeastSquaresBound.lean#L12-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory GlobalTheory.WeightedLS
open Matrix
variable {M g : ℕ}

theorem GlobalTheory.WeightedLS.det_pos (L : Matrix (Fin M) (Fin g) ℝ) (hL : L.rank = g) (D : Fin M → ℝ)
    (hD : ∀ k, 0 < D k) : 0 < (L.transpose * Matrix.diagonal D * L).det := by sorry
