-- Prove2me | Theorems.Thm_LosslessQLTC_corollary_4_5
-- name    : LosslessQLTC.corollary_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:24.622133+00:00
-- url     : https://prove2.me/theorems/b3aee9dd-bcff-412b-b100-6e406ef09631
-- title:
--   Corollary 4.5, p.33 — iterated excess bound
-- statement:
--   For every $0\le i\le r+1$,
--
--   $$\|E_i\|\le\sum_{j=1}^i\frac{(k-j)!}{(k-i)!}\big(\|\mathrm{Same}_j\|+\|\mathrm{Light}_j\|\big).$$
--
--   This reduces the excess to the level charges alone.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: the heavy set $H_r\subseteq V_r$ → a cochain $f$ with $H_r=\operatorname{supp}f$, thresholds $\gamma:\mathbb N\to\mathbb R$ used at $i<r$; reason: the source identifies a cochain with its support; same instances
--   - reading: $H_r(t)$, $\|\mathrm{Same}_i\|$, $\|\mathrm{Light}_i\|$ used without a printed definition → $H_r\cap H(t)$, $\sum_{a\in H_i}\|a\|\mathrm{Same}(a)$, $\sum_{a\in H_i}\|a\|\mathrm{Light}(a)$; reason: their use on pp.29–32 and p.39 fixes these
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Corollary 4.5, p.33, eq. (4.16)

import Mathlib
import Definitions.Def_LosslessQLTC_Heavy

namespace LosslessQLTC

/-- Corollary 4.5 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.33): for every
`0 ≤ i ≤ r + 1`, `∥E_i∥ ≤ Σ_{j=1}^i ((k − j)! / (k − i)!) (∥Same_j∥ + ∥Light_j∥)` (4.16).

**Formalization Note.** `j ≤ i ≤ r + 1 ≤ k`, so both natural-number subtractions are true ones. -/
theorem corollary_4_5 {k r : ℕ} (X : SquareComplex k) (hr : r < k) (f : Level X r → ZMod 2)
    (γ : ℕ → ℝ) (hγ : IsThresholds k r γ) (i : ℕ) (hi : i ≤ r + 1) :
    excessNorm X f γ i ≤
      ∑ j ∈ Finset.Icc 1 i, (((k - j).factorial : ℝ) / ((k - i).factorial : ℝ)) *
        (sameNorm X f γ j + lightNorm X f γ j) := by sorry

end LosslessQLTC
