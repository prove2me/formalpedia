-- Prove2me | Theorems.Thm_Matrix_existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent
-- name    : Matrix.existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/d05cb42f-bbf1-516c-a1a8-f34c2df2fcc6
-- title:
--   Unique solution of y + D y⁽ᵖ⁾ = b for nilpotent-triangular D
-- statement:
--   Let $S$ be a commutative ring, $p$ a prime, and suppose $S$ has characteristic $p$. Let $d$ be a natural number, let $\mathfrak{n}$ be an ideal of $S$ which is nilpotent as an element of the multiplicative monoid of ideals, i.e. $\mathfrak{n}^k = 0$ for some $k$, and let $D$ be a $d \times d$ matrix over $S$ whose entries $D_{ij}$ lie in $\mathfrak{n}$ for all indices with $j \le i$, that is, on and below the diagonal (so $D$ is strictly upper triangular modulo $\mathfrak{n}$). Then for every vector $b \in S^d$ there is exactly one vector $y \in S^d$ satisfying $$y + D \cdot (y_j^p)_j = b,$$ where $D \cdot (-)$ denotes matrix–vector multiplication applied to the vector whose $j$-th coordinate is $y_j^p$; equivalently, the $\sigma$-semilinear system $y + D\,\sigma(y) = b$ with $\sigma$ the coordinatewise $p$-th power map has a unique solution.
--
--   This is the back-substitution lemma of semilinear algebra in characteristic $p$: a Frobenius-twisted triangular system with nilpotent-valued entries on and below the diagonal is uniquely solvable. It is used in the construction of Fontaine lifts, where it supplies the bijectivity of the $w$-series map under an invertibility hypothesis on the linear part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Matrix.existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    {d : ℕ} (𝔫 : Ideal S) (h𝔫 : IsNilpotent 𝔫)
    (D : Matrix (Fin d) (Fin d) S) (hD : ∀ i j : Fin d, j ≤ i → D i j ∈ 𝔫)
    (b : Fin d → S) :
    ∃! y : Fin d → S, y + D.mulVec (fun j => y j ^ p) = b := by sorry
