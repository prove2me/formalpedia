-- Prove2me | Theorems.Thm_LinfContractionFP_section_5_restricted_maps
-- name    : LinfContractionFP.section_5_restricted_maps
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:16:32.316294+00:00
-- url     : https://prove2.me/theorems/33b611d2-e958-4523-acb6-23b66d601190
-- title:
--   Section 5 — restricted maps are contractions of dimension $\le d/2$
-- statement:
--   Let $0<\gamma\le1$ and let $f$ be a $(1-\gamma)$-contraction of $[0,1]^d$, extended by clipping.
--
--   1. For every set $S$ of coordinates and every point $q$, the map $y\mapsto f_S(y,q_{-S})$ is a $(1-\gamma)$-contraction of $[0,1]^S$.
--   2. For every vector $w\in\mathbb R^d$ with median $t$, the sets $\{i:w_i<t\}$ and $\{i:w_i>t\}$ have at most $d/2$ elements.
--
--   Applied to the narrow and wide coordinates of Algorithm 2, these say that its two recursive problems are contraction problems of at most half the dimension.
--
--   Differences from the source:
--   - generalization: the maps y ↦ f_N(y, q_{−N}) and y ↦ f_W(q_{−W}, y) for the centre q of the box → every set S of coordinates and every point q; reason: N, W and the centre are instances
--   - reading: median; dimension at most d/2 → lower median; 2|S| ≤ d; reason: the lower median gives both bounds; any median with this property is what the proof uses
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 5, p.8

import Mathlib
import Definitions.Def_LinfContractionFP_IsContraction
import Definitions.Def_LinfContractionFP_restrictMap
import Definitions.Def_LinfContractionFP_lowerMedian

open scoped Classical

namespace LinfContractionFP

/-- Section 5: the restricted maps are contractions, and the narrow and wide sets of the median
split have at most `d/2` elements. For every set `S` of coordinates and every point `q` (the box
centre), `y ↦ f_S(y, q_{−S})` is a `(1 − γ)`-contraction of `[0,1]^S`; and for every vector `w`
of half side lengths with (lower) median `t`, `|{i : w_i < t}| ≤ d/2` and `|{i : w_i > t}| ≤ d/2`.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Section 5, p.8: "The algorithm recursively invokes Solve at precision γη/2 on the maps
y ↦ f_N(y, q_{−N}) and y ↦ f_W(q_{−W}, y). Both maps are (1 − γ)-contractions on their unit
cubes, since fixing input coordinates and restricting output coordinates preserve the
contraction property. Each recursive problem has dimension at most d/2."

**Formalization Note.** The maps use the clipped extension (`restrictMap`), so `q` may be any
point. "At most d/2" is `2 |S| ≤ d`. -/
theorem section_5_restricted_maps {ι : Type} [Fintype ι] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (f : (ι → ℝ) → (ι → ℝ)) (hf : IsContraction γ f) :
    (∀ (S : Finset ι) (q : ι → ℝ), IsContraction γ (restrictMap f S q)) ∧
      ∀ w : ι → ℝ,
        2 * (Finset.univ.filter fun i => w i < lowerMedian w).card ≤ Fintype.card ι ∧
          2 * (Finset.univ.filter fun i => w i > lowerMedian w).card ≤ Fintype.card ι := by sorry

end LinfContractionFP
