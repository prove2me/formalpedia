-- Prove2me | Theorems.Thm_LawLocalComp_lemma_3_2
-- name    : LawLocalComp.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:21.023739+00:00
-- url     : https://prove2.me/theorems/0fa38adc-2399-4c68-a31b-0a32bf9cc4fe
-- title:
--   Lemma 3.2 (Logarithmic center packing)
-- statement:
--   Let $m,H\ge1$ be integers, $A>0$, $x_i=A(1+1/m)^i$ for $0\le i<mH$, and let $c_1,\dots,c_s$ be $s\ge1$ arbitrary positive centers. If $s<mH/4$, then at least half of the grid points lie at logarithmic distance at least $H/(16s)$ from every center:
--   $$\#\Big\{i<mH:\ |\ln x_i-\ln c_j|\ge\tfrac{H}{16s}\ \text{for all } j\Big\}\ \ge\ \tfrac{mH}{2}.$$
--   This packing bound is the final counting step of the conditional-mean lower bounds.
--
--   Differences from the source: none.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 3.2, p.5

import Mathlib

namespace LawLocalComp

/-- **Lemma 3.2 (Logarithmic center packing).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 3.2, p.5.

Let `m, H ≥ 1` be integers, `A > 0`, `x_i = A(1 + 1/m)^i` for `0 ≤ i < mH`, and let `s ≥ 1` positive
centers `c_1, …, c_s` be arbitrary. If `s < mH/4`, at least half of the grid points lie at logarithmic
distance at least `H/(16s)` from every center. -/
theorem lemma_3_2 (m H : ℕ) (hm : 1 ≤ m) (hH : 1 ≤ H) (A : ℝ) (hA : 0 < A) (s : ℕ) (hs : 1 ≤ s)
    (c : Fin s → ℝ) (hc : ∀ j, 0 < c j) (hsmall : (s : ℝ) < m * H / 4) :
    (m * H : ℝ) / 2 ≤ ((Finset.range (m * H)).filter (fun i => ∀ j, (H : ℝ) / (16 * s) ≤
      |Real.log (A * (1 + 1 / (m : ℝ)) ^ i) - Real.log (c j)|)).card := by sorry

end LawLocalComp
