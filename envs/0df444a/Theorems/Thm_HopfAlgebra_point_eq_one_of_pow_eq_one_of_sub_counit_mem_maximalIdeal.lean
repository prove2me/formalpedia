-- Prove2me | Theorems.Thm_HopfAlgebra_point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal
-- name    : HopfAlgebra.point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/94f743d7-2f8f-5769-b48e-54fddadaaece
-- title:
--   Finite-order points congruent to the counit are trivial
-- statement:
--   Let $O$ be a commutative domain which is a discrete valuation ring, let $\ell$ be a prime with $\ell \neq 2$, and assume the image of $\ell$ in $O$ is irreducible, i.e. $\ell$ is a uniformiser of $O$. Let $H$ be a commutative ring carrying a Hopf algebra structure over $O$, finite and flat as an $O$-module, and with cocommutative comultiplication. Let $x$ be an element of `WithConv (H →ₐ[O] O)`, that is an $O$-algebra homomorphism $H \to O$ regarded as a point of the group of $O$-points of $\operatorname{Spec} H$ under the convolution product, whose unit is the counit. Assume that $x$ is congruent to the counit modulo the maximal ideal of $O$, in the sense that $x(h) - \varepsilon(h) \in \mathfrak{m}_O$ for every $h \in H$, where $\varepsilon$ denotes the counit of $H$ (its value being transported along the identity algebra map of $O$). Assume finally that $x$ has finite order: $x^n = 1$ in the convolution group for some integer $n > 0$. Then $x = 1$, i.e. $x$ is the counit.
--
--   This is the point-theoretic form of the triviality of torsion points congruent to the identity on a finite flat commutative group scheme over a discrete valuation ring of absolute ramification index $1$ and odd residue characteristic, in the range covered by Raynaud's bound $e < \ell - 1$. It extends the $\ell$-power-order case to arbitrary positive order and is used in the analysis of the inertial behaviour of finite flat Galois representations, for instance in [`GaloisRep.finiteFlat_point_mem_of_valuation_sub_counit_lt_one_of_inertia_displacement_mem`](thm.html#GaloisRep.finiteFlat_point_mem_of_valuation_sub_counit_lt_one_of_inertia_displacement_mem) and in the comparison of such points with the counit over $\mathbb{Z}_\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal.lean

import Definitions.Def_GaloisRep_Flat
import Mathlib.RingTheory.DiscreteValuationRing.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hunif : Irreducible (ℓ : O))
    (H : Type*) [CommRing H] [HopfAlgebra O H] [Module.Finite O H] [Module.Flat O H]
    [Coalgebra.IsCocomm O H]
    (x : WithConv (H →ₐ[O] O))
    (hx1 : ∀ h : H, x h - algebraMap O O (Coalgebra.counit h) ∈ IsLocalRing.maximalIdeal O)
    (n : ℕ) (hn : 0 < n) (hxn : x ^ n = 1) :
    x = 1 := by sorry
