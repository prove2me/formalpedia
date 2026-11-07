-- Prove2me | Theorems.Thm_LosslessQLTC_theorem_4_4
-- name    : LosslessQLTC.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:30.68029+00:00
-- url     : https://prove2.me/theorems/abca0858-8f17-4775-8035-547a90b0d9fb
-- title:
--   Theorem 4.4, p.32 — excess recursion
-- statement:
--   For every $1\le i\le r+1$,
--
--   $$\|E_i\|\le(k-i+1)\|E_{i-1}\|+\|\mathrm{Same}_i\|+\|\mathrm{Light}_i\|.$$
--
--   This is the level-by-level form of the recursive excess bound.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: the heavy set $H_r\subseteq V_r$ → a cochain $f$ with $H_r=\operatorname{supp}f$, thresholds $\gamma:\mathbb N\to\mathbb R$ used at $i<r$; reason: the source identifies a cochain with its support; same instances
--   - reading: $H_r(t)$, $\|\mathrm{Same}_i\|$, $\|\mathrm{Light}_i\|$ used without a printed definition → $H_r\cap H(t)$, $\sum_{a\in H_i}\|a\|\mathrm{Same}(a)$, $\sum_{a\in H_i}\|a\|\mathrm{Light}(a)$; reason: their use on pp.29–32 and p.39 fixes these
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Theorem 4.4, p.32, eq. (4.15)

import Mathlib
import Definitions.Def_LosslessQLTC_Heavy

namespace LosslessQLTC

/-- Theorem 4.4 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.32): for every
`1 ≤ i ≤ r + 1`, `∥E_i∥ ≤ (k − i + 1) ∥E_{i−1}∥ + ∥Same_i∥ + ∥Light_i∥` (4.15). -/
theorem theorem_4_4 {k r : ℕ} (X : SquareComplex k) (hr : r < k) (f : Level X r → ZMod 2)
    (γ : ℕ → ℝ) (hγ : IsThresholds k r γ) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ r + 1) :
    excessNorm X f γ i ≤
      ((k : ℝ) - i + 1) * excessNorm X f γ (i - 1) + sameNorm X f γ i + lightNorm X f γ i := by sorry

end LosslessQLTC
