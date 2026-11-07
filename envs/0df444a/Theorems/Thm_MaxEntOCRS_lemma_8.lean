-- Prove2me | Theorems.Thm_MaxEntOCRS_lemma_8
-- name    : MaxEntOCRS.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:46.018754+00:00
-- url     : https://prove2.me/theorems/a4904420-e073-4cf0-913e-9c5279e050a5
-- title:
--   Lemma 8 — global bound $x^{\mathsf T}\Delta y \le r\sum_i p_i z_i$
-- statement:
--   Let $\nu$ be a right-half-plane zero-free probability distribution on the subsets of a finite index set, with $p_i$ and $\Delta$ as in Eq. (2). For all $x, y \in \mathbb R^k_{\ge 0}$, with $z = (x + y)/2$ and $r = \max_i z_i$,
--   $$
--   x^{\mathsf T} \Delta y = \sum_{i,j} x_i \Delta_{ij} y_j \le r \sum_i p_i z_i .
--   $$
--   The statement is proved for every $r \ge \max_i z_i$. It bounds the total cross term of $K$ in the closing argument of Theorem 2.
--
--   Differences from the source:
--   - generalization: r = max_i z_i → every r with z_i ≤ r for all i; reason: the right side increases in r because Σ_i p_i z_i ≥ 0, so r = max_i z_i is a special case; this also covers the empty index set
--   - encoding: ν a right-half-plane zero-free distribution on 2^[k] → ν : Finset ι → ℝ on a finite type ι with ν ≥ 0, Σ ν = 1 and IsRHPZeroFree ν; reason: a law is a nonnegative function of total mass 1; same objects
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Lemma 8, p.7 (proof in A.6, p.14)

import Mathlib
import Definitions.Def_MaxEntOCRS_IsRHPZeroFree
import Definitions.Def_MaxEntOCRS_incProb
import Definitions.Def_MaxEntOCRS_DeltaMat

namespace MaxEntOCRS

/-- Lemma 8 (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.7; A.6, p.14): if `ν` is right-half-plane zero-free, then for all
nonnegative vectors `x, y`, with `z = (x + y)/2` and `r = max_i z_i`,
`xᵀΔy ≤ r ∑_i p_i z_i`. Stated for every upper bound `r` of the `z_i`, which contains the case
`r = max_i z_i`. -/
theorem lemma_8 {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Finset ι → ℝ)
    (hν0 : ∀ F, 0 ≤ ν F) (hν1 : ∑ F, ν F = 1) (hν : IsRHPZeroFree ν)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (r : ℝ)
    (hr : ∀ i, (x i + y i) / 2 ≤ r) :
    ∑ i, ∑ j, x i * DeltaMat ν i j * y j ≤ r * ∑ i, incProb ν i * ((x i + y i) / 2) := by sorry

end MaxEntOCRS
