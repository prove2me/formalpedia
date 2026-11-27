-- Prove2me | Theorems.Thm_LL_SquareWave1124_leaf_square_wave_weight_sums
-- name    : LL_SquareWave1124.leaf_square_wave_weight_sums
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-27T05:50:06.576599+00:00
-- url     : https://prove2.me/theorems/598c0939-e9dc-41ef-ac83-47f195311183
-- title:
--   Two sums of the weight $W_\Delta(h)=\min(|h|^{-1},\Delta^{-1}h^{-2})$
-- statement:
--   There is $C>0$ such that for every $0<\Delta\le1/4$ and every integer $H\ge1$: $\sum_{|h|\le H}W_\Delta(h)\le C(1+\log(1/\Delta))$, and $\sum_{h\in S}W_\Delta(h)\le C/(\Delta H)$ for every finite set $S$ of integers disjoint from $[-H,H]$.
-- source:
--   Brüdern and Perelli 1998, Section 7, page 370, the sums after display (40).

import Mathlib
import Definitions.Def_LL_SquareWave1124_sqW

namespace LL_SquareWave1124
theorem leaf_square_wave_weight_sums :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 → ∀ H : ℕ, 1 ≤ H →
      (∑ h ∈ Finset.Icc (-(H : ℤ)) H, sqW Δ h) ≤ C * (1 + Real.log (1 / Δ)) ∧
      ∀ S : Finset ℤ, Disjoint S (Finset.Icc (-(H : ℤ)) H) →
        (∑ h ∈ S, sqW Δ h) ≤ C / (Δ * H) := by sorry
end LL_SquareWave1124
