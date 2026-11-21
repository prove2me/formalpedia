-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_idxMap_of_mem_Ico
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.idxMap_of_mem_Ico
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T07:56:59.61536+00:00
-- url     : https://prove2.me/theorems/a7906fd2-b8d9-47c3-a5e6-faf80fb0cd09
-- title:
--   idxMap of mem Ico
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.idxMap_of_mem_Ico` is extracted from `LevyStochCalc.Brownian.SimplePredictableRefineInvariance`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Refinement of a simple predictable integrand

Refining a `SimplePredictable Ω T` onto a finer partition
(`SimplePredictable.refine`), the pointwise description of the refined
integrand (`SimplePredictable.refine_eval`), and the invariance of the simple
stochastic integral under such a refinement
(`SimplePredictable.simpleIntegral_refine`), obtained by telescoping the driving
increments over each fiber of the refining index map.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.idxMap_of_mem_Ico
    {T : ℝ} (H : SimplePredictable Ω T)
    {M : ℕ} {π' : Fin (M + 1) → ℝ}
    (h_strictMono : StrictMono π')
    {idxMap : Fin M → Fin H.N}
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    {i : Fin H.N} {k_lo k_hi : Fin (M + 1)}
    (hk_lo : π' k_lo = H.partition i.castSucc)
    (hk_hi : π' k_hi = H.partition i.succ)
    {n : ℕ} (h_lt : n < M) (hn_lo : k_lo.val ≤ n) (hn_hi : n < k_hi.val) :
    idxMap ⟨n, h_lt⟩ = i := by sorry
