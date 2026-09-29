-- Prove2me | Theorems.Thm_GCTOcc_row_extended_rectangle_occurs
-- name    : GCTOcc.row_extended_rectangle_occurs
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T17:44:21.952887+00:00
-- url     : https://prove2.me/theorems/a3397022-e459-48bc-abeb-e8440b27d961
-- title:
--   Proposition 2.3 — row extended even rectangles occur in $\mathbb{C}[\Omega_n]_k$
-- statement:
--   Let $k \ge 1$ and let $\ell$ be even with $k\ell \le n$. Consider the rectangle $k \times \ell$ — the partition with $k$ parts all equal to $\ell$ — and extend its first row so that the total number of boxes becomes $nk$. The resulting **row extended rectangle**
--
--   $$(k\times\ell)^{\square nk} \;=\; \big(\ell + (nk - k\ell),\; \underbrace{\ell,\dots,\ell}_{k-1}\big)$$
--
--   occurs in the degree $k$ part of the coordinate ring of $\Omega_n$.
--
--   These shapes are the basic building blocks of the proof of the main theorem: combined with the semigroup property of Lemma 2.2, they generate every partition with a long first row and a body decomposable into even rectangles, which by the Kadish–Landsberg restriction covers the candidate occurrence obstructions of large degree. The proof evaluates explicit highest weight vectors on the padded power sums supplied by Theorem 2.5, using the nonvanishing of the fundamental invariant of a form space at a power sum.
--
--   **Formalization note.** The weight is given directly as the function $i \mapsto \ell + (nk-k\ell)$ for $i = 0$, $\ell$ for $1 \le i < k$, and $0$ otherwise; under the hypotheses it is a partition of $nk$ with at most $n^2$ parts, as verified separately.
-- source:
--   P. Bürgisser, C. Ikenmeyer, G. Panova, *No occurrence obstructions in geometric complexity theory*, J. Amer. Math. Soc. 32 (2019), 163–193, https://doi.org/10.1090/jams/908, p. 167, Proposition 2.3 (with the notation $\lambda^{\square D}$ for the lifted shape introduced just above it).

import Definitions.Def_GCTOcc_occurrence
open MvPolynomial

namespace GCTOcc

theorem row_extended_rectangle_occurs (n k l : ℕ) (hk : 1 ≤ k) (hn : k * l ≤ n) (hl : Even l) :
    Occurs n k (fun i => if i = 0 then l + (n * k - k * l) else if i < k then l else 0)
      (orbitClosure n (detPoly n)) := by sorry

end GCTOcc
