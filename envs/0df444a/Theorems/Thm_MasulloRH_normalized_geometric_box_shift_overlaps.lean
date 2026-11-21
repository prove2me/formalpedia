-- Prove2me | Theorems.Thm_MasulloRH_normalized_geometric_box_shift_overlaps
-- name    : MasulloRH.normalized_geometric_box_shift_overlaps
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:16:06.327183+00:00
-- url     : https://prove2.me/theorems/fa50948f-56da-4d20-8046-d2063aeeba8d
-- title:
--   Normalized geometric orbit cutoffs realizing simultaneous prime-power shift ratios
-- statement:
--   Let $I$ be a finite set, choose $0<r_i<1$, and put independent normalized geometric weights $w_N(x)=\prod_{i\in I}\big(r_i^{x_i}/\sum_{j=0}^N r_i^j\big)$ on the box $\{0,\ldots,N\}^I$, with each denominator belonging to its own coordinate. These weights sum to one. For any nonnegative integer shift vector $d$, sum $w_N(x)w_N(x+d)$ over the points for which both arguments lie in the box. As $N$ tends to infinity this overlap tends to $$\prod_{i\in I}\left(r_i^{d_i}\frac{1-r_i}{1+r_i}\right).$$ In particular for a fixed finite set of rational primes and $r_p=p^{-1/2}$ the limiting overlap relative to zero shift equals $\prod_p p^{-d_p/2}$. This realizes the ratios by positive finite orbit cutoffs and determines their absolute scale.
-- source:
--   Orbit cutoff repair for Masullo, The Music of the Primes, (11.3.2.2) and (12.2.2.1). Builds on the earlier single-shift overlap bound https://prove2.me/theorems/1d6ad290-71d8-4e54-83c3-83d1c09ede6c and directed cutoff theorem https://prove2.me/theorems/f5a8e538-7087-4814-a19f-922bc9aad777.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open Filter Finset
open scoped Topology

theorem MasulloRH.normalized_geometric_box_shift_overlaps {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hr' : ∀ i, r i < 1) :
    let w (N : ℕ) (x : ι → ℕ) := ∏ i, (r i)^(x i) / (∑ k ∈ range (N+1), (r i)^k)
    (∀ N, (∑ x ∈ Fintype.piFinset (fun _ : ι => range (N+1)), w N x) = 1) ∧
    (∀ d : ι → ℕ, Tendsto (fun N : ℕ => ∑ x ∈ Fintype.piFinset (fun i => range (N+1-d i)),
      w N x * w N (fun i => x i + d i)) atTop
      (𝓝 (∏ i, (r i)^(d i) * ((1-r i)/(1+r i))))) := by sorry
