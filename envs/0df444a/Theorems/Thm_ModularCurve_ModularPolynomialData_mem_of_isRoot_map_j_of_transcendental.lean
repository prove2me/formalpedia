-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental
-- name    : ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/32dd0688-a2b7-5e48-b76f-7914181d8c1e
-- title:
--   Roots of Φ_N(j(W),Y) lie in the N-torsion field
-- statement:
--   Let $N$ be a nonzero natural number and let $\mathbb{K}$ denote the field of Hahn series with exponents in $\mathbb{Q}$ and coefficients in $\overline{\mathbb{Q}}$. Let `data` be a `ModularPolynomialData N`, that is, a polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic, of degree in $Y$ equal to $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which vanishes when $X$ is substituted by the $q$-expansion of $j$ and $Y$ by that of $j(q^N)$. Let $W$ be a Weierstrass curve over $\mathbb{K}$ whose discriminant is a unit, and assume its $j$-invariant is transcendental over $\mathbb{Q}$. Let $L$ be a subfield of $\mathbb{K}$ containing the five coefficients $a_1, a_2, a_3, a_4, a_6$ of $W$ and such that, for every nonsingular affine point $(x,y)$ of $W$ killed by $N$ in the group of points, both $x$ and $y$ lie in $L$. Then every root $r \in \mathbb{K}$ of the one-variable polynomial over $\mathbb{K}$ obtained from $\Phi$ by mapping each coefficient in $\mathbb{Z}[X]$ to its value at $j(W)$ — that is, of $\Phi(j(W), Y)$ — lies in $L$.
--
--   This is the statement that the $\psi(N)$ roots of the specialised modular polynomial $\Phi_N(j(W),Y)$, namely the $j$-invariants of the quotients of $W$ by its cyclic subgroups of order $N$, are defined over any field of definition of $W$ together with its $N$-torsion coordinates; it removes the parity restriction from the corresponding statement for odd $N$. It is used in the computations of the divisibility properties of the order of $\bar{j}$ and of $\bar{j} - 1728$ over the Hahn field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental
    {N : ℕ} [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic] (ht : Transcendental ℚ W.j)
    (L : Subfield (HahnSeries ℚ (AlgebraicClosure ℚ)))
    (h₁ : W.a₁ ∈ L) (h₂ : W.a₂ ∈ L) (h₃ : W.a₃ ∈ L) (h₄ : W.a₄ ∈ L) (h₆ : W.a₆ ∈ L)
    (htors : ∀ (x y : HahnSeries ℚ (AlgebraicClosure ℚ)) (h : W.toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 → x ∈ L ∧ y ∈ L)
    (r : HahnSeries ℚ (AlgebraicClosure ℚ))
    (hr : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)).IsRoot r) :
    r ∈ L := by sorry
