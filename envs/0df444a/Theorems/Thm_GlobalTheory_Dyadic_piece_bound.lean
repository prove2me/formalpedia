-- Prove2me | Theorems.Thm_GlobalTheory_Dyadic_piece_bound
-- name    : GlobalTheory.Dyadic.piece_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:48.510833+00:00
-- url     : https://prove2.me/theorems/7a1f15e1-7a44-4f2b-a2fb-284147e92c71
-- title:
--   Dyadic: piece bound
-- statement:
--   The Dyadic construction uses the piece bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LintegralBoundByDyadicSummation.lean#L63-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LintegralBoundByDyadicSummation.lean#L63-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LintegralBoundByDyadicSummation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.Dyadic

theorem GlobalTheory.Dyadic.piece_bound (r kk : ℕ) (H De D l l' u v : ℝ) (hr : 1 ≤ r) (hkk : 1 ≤ kk) (hH : 1 ≤ H)
    (hDe : 1 ≤ De) (hD : 0 < D) (hl : 1 ≤ l) (hl' : 1 ≤ l') (hu : 0 < u) (hv : 0 < v)
    (h1 : (r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / u *
      ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / v) * D ≤ 2 ^ r)
    (h2 : D ≤ (l * l' * H) ^ (2 * r)) :
    ((l * l' * H) ^ (10 * r ^ 3) * ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / u) ^ kk *
        (l ^ (24 * r ^ 3 + 1))⁻¹) *
      ((l * l' * H) ^ (10 * r ^ 3) * ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / v) ^ kk *
        (l' ^ (24 * r ^ 3 + 1))⁻¹) ≤
      (r : ℝ) ^ (2 * r) * H ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ kk *
        (l⁻¹ * l'⁻¹ * u⁻¹ * v⁻¹) := by sorry
