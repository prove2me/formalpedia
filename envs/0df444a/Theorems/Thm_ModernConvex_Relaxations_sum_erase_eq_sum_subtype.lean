-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_sum_erase_eq_sum_subtype
-- name    : ModernConvex.Relaxations.sum_erase_eq_sum_subtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:16:07.227007+00:00
-- url     : https://prove2.me/theorems/8600e565-9ea0-43e2-bedf-ce24731018a0
-- title:
--   A sum over `univ.erase i` is a sum over the complement subtype
-- statement:
--   **Reindexing a sum over a `Finset.erase` as a sum over a subtype.**
--
--   For a finite index type $\mathrm{Fin}\,n$, an element $i$, and any real-valued function $g$,
--   $$\sum_{j\in\{1,\dots,n\}\setminus\{i\}} g(j) \;=\; \sum_{j\,:\,\mathrm{Fin}\,n,\ j\ne i} g(j).$$
--   The left side is a sum over a `Finset` (the complement of $i$ in the universal finset); the right side is a sum over the subtype of elements different from $i$.
--
--   The two are related by the evident bijection $j\mapsto\langle j,\ j\ne i\rangle$, so the identity follows from `Finset.sum_bij`. It is the bridge needed when a quadratic form is written as a sum over `Finset.univ.erase i` (the Schur form) but the corresponding matrix is indexed by the complement subtype (the Schur complement) — i.e. exactly when proving that the quadratic form of the Schur complement at a pivot equals the Schur form.
-- source:
--   Finset.sum_bij applied to the subtype equivalence; reindexing lemma for the Schur-complement PSD oracle of the MAXCUT SDP.

import Mathlib

open scoped BigOperators

namespace ModernConvex.Relaxations

/-- Sums over `Finset.univ.erase i` reindex as sums over the complement subtype. -/
theorem sum_erase_eq_sum_subtype {n : ℕ} (i : Fin n) (g : Fin n → ℝ) :
    (∑ j ∈ Finset.univ.erase i, g j) = ∑ j : {j : Fin n // j ≠ i}, g j.1 := by sorry

end ModernConvex.Relaxations
