-- Prove2me | Theorems.Thm_LosslessQLTC_eq_2_2
-- name    : LosslessQLTC.eq_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:18:20.172724+00:00
-- url     : https://prove2.me/theorems/54ec7942-d45a-4ae5-accc-e31cb1f952c0
-- title:
--   Eq. (2.2), p.17 — the norm identity for $\delta 1_{\{v\}}$
-- statement:
--   Let $v\in V_I$ with $|I|<k$. For $i\notin I$, the total weight of the neighbours of $v$ in direction $i$ is $D_i/D_{I\cup\{i\}}=\|v\|$. Summing over the upward directions gives
--
--   $$\|\delta_{|I|}1_{\{v\}}\|=\sum_{v\lessdot w}\|w\|=\sum_{i\notin I}\frac{D_i}{D_{I\cup\{i\}}}=(k-|I|)\|v\|.$$
--
--   This identity converts between the norm of a vertex and the norm of its upward neighbourhood.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), eq. (2.2), p.17

import Mathlib
import Definitions.Def_LosslessQLTC_normC

namespace LosslessQLTC

/-- Eq. (2.2) (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.17): for `v ∈ V_I` and `i ∉ I`
the total weight of the neighbours of `v` in direction `i` is `D_i / D_{I ∪ {i}} = ∥v∥`, and
`∥δ_{|I|} 1_{v}∥ = Σ_{v ⋖ w} ∥w∥ = Σ_{i ∉ I} D_i / D_{I ∪ {i}} = (k − |I|) ∥v∥`.

**Formalization Note.** `δ_s` has domain `0 ≤ s < k` in the source (p.16), hence `s < k`. -/
theorem eq_2_2 {k s : ℕ} (X : SquareComplex k) (hs : s < k) (v : Level X s) :
    (∀ i, i ∉ X.type v.1 →
      (∑ w : Level X (s + 1),
          if X.up v.1 w.1 ∧ X.type w.1 = insert i (X.type v.1) then weight X w.1 else 0) =
        (X.D i : ℝ) / (prodD X.D (insert i (X.type v.1)) : ℝ) ∧
      (X.D i : ℝ) / (prodD X.D (insert i (X.type v.1)) : ℝ) = weight X v.1) ∧
    normC X (delta X s (Pi.single v 1)) =
      (∑ w : Level X (s + 1), if X.up v.1 w.1 then weight X w.1 else 0) ∧
    (∑ w : Level X (s + 1), if X.up v.1 w.1 then weight X w.1 else 0) =
      ∑ i ∈ Finset.univ \ X.type v.1,
        (X.D i : ℝ) / (prodD X.D (insert i (X.type v.1)) : ℝ) ∧
    (∑ i ∈ Finset.univ \ X.type v.1,
        (X.D i : ℝ) / (prodD X.D (insert i (X.type v.1)) : ℝ)) =
      ((k : ℝ) - s) * weight X v.1 := by sorry

end LosslessQLTC
