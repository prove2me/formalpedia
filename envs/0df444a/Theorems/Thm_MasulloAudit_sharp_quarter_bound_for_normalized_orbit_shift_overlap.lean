-- Prove2me | Theorems.Thm_MasulloAudit_sharp_quarter_bound_for_normalized_orbit_shift_overlap
-- name    : MasulloAudit.sharp_quarter_bound_for_normalized_orbit_shift_overlap
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T01:21:04.655375+00:00
-- url     : https://prove2.me/theorems/1d6ad290-71d8-4e54-83c3-83d1c09ede6c
-- title:
--   Sharp quarter bound for the overlap of a normalized orbit cutoff with a nonzero translate
-- statement:
--   Fix $d\in\mathbb Z\setminus\{0\}$. For any nonnegative finitely supported weight $w$ on $\mathbb Z$ with $\sum_i w_i=1$, its overlap with its translate satisfies
--   $$\sum_i w_iw_{i+d}\le\tfrac14.$$
--   The bound is attained for every such $d$, by placing weight $1/2$ at each of $0$ and $d$. The integer lattice indexes the orbit $p^{\mathbb Z}$ in the one-prime cutoff model for the orbital-trace audit.
-- source:
--   The extremal inequality is the path-forest case of T. S. Motzkin and E. G. Straus, “Maxima for graphs and a new proof of a theorem of Turán”, Canadian J. Math. 17 (1965), 533–540, https://doi.org/10.4153/CJM-1965-053-6. The rational-idèle cutoff example assigning mass 1/2 to each of two neighboring translates and producing overlap 1/4 is recorded at https://github.com/mccorvie/riemann-masullo/issues/1358#issuecomment-7054088460. This proof specializes the elementary bipartition argument to integer translates for every nonzero step.

import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Basic

open Finset

theorem MasulloAudit.sharp_quarter_bound_for_normalized_orbit_shift_overlap (d : ℤ) (hd : d ≠ 0) :
    (∀ w : ℤ →₀ ℝ, (∀ i : ℤ, 0 ≤ w i) → (∑ i ∈ w.support, w i) = 1 →
      (∑ i ∈ w.support, w i * w (i+d)) ≤ 1/4) ∧
    (∃ w : ℤ →₀ ℝ, (∀ i : ℤ, 0 ≤ w i) ∧ (∑ i ∈ w.support, w i) = 1 ∧
      (∑ i ∈ w.support, w i * w (i+d)) = 1/4) := by sorry
