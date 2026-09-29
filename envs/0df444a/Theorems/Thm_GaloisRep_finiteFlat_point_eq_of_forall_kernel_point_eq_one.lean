-- Prove2me | Theorems.Thm_GaloisRep_finiteFlat_point_eq_of_forall_kernel_point_eq_one
-- name    : GaloisRep.finiteFlat_point_eq_of_forall_kernel_point_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/4ffe4688-50af-5094-8a1a-e631f5835574
-- title:
--   Injectivity of reduction from triviality of kernel points
-- statement:
--   Let $\ell$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$ (the predicate `LiesOverPrime`, i.e. the image of $\ell$ lies in `A.nonunits`). Write $\mathbb Z_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb Q$ consisting of the rationals whose denominator is coprime to $\ell$. Let $H$ be a commutative ring carrying a Hopf algebra structure over $\mathbb Z_{(\ell)}$ which is finite and flat as a $\mathbb Z_{(\ell)}$-module and whose comultiplication is cocommutative, and consider the monoid `WithConv (H →ₐ[ℤ_{(ℓ)}] AlgebraicClosure ℚ)` of $\mathbb Z_{(\ell)}$-algebra maps $H \to \overline{\mathbb Q}$ under convolution, whose unit $1$ is the point $h \mapsto$ the image of `Coalgebra.counit h`. Let $k$ be a natural number and assume: (i) every such point $f$ satisfies $f^{\ell^k} = 1$; (ii) every point $\varphi$ that is fixed pointwise by the decomposition subgroup of $A$ in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (i.e. $\sigma(\varphi h) = \varphi h$ for all $h \in H$ and all $\sigma$ in `A.decompositionSubgroup ℚ`), which satisfies $v_A(\varphi h - \varepsilon(h)) < 1$ for all $h \in H$, and which satisfies $\varphi^{\ell^k} = 1$, is equal to $1$. Then for any two decomposition-subgroup-fixed points $f$ and $g$ with $v_A(f h - g h) < 1$ for all $h \in H$ one has $f = g$.
--
--   This is the injectivity of reduction modulo the maximal ideal of $A$ on the $\overline{\mathbb Q}$-points of a finite flat commutative group scheme over $\mathbb Z_{(\ell)}$, deduced from the corresponding statement for points reducing to the identity: the difference $f g^{-1}$ of two points with the same reduction is a kernel point. It feeds the variant [`GaloisRep.finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one`](thm.html#GaloisRep.finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one), in the analysis of the local behaviour at $\ell$ of finite flat group schemes used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_finiteFlat_point_eq_of_forall_kernel_point_eq_one.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.finiteFlat_point_eq_of_forall_kernel_point_eq_one
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H]
    [Module.Finite (GaloisRep.ratLocalizedAt ℓ) H] [Module.Flat (GaloisRep.ratLocalizedAt ℓ) H] [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) H]
    (k : ℕ) (hord : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ), f ^ ℓ ^ k = 1)
    (hker : ∀ φ : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ), (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (φ h) = φ h) → (∀ h : H, A.valuation (φ h - algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) → φ ^ ℓ ^ k = 1 → φ = 1)
    (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)) (hf : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (f h) = f h)) (hg : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (g h) = g h))
    (hfg : ∀ h : H, A.valuation (f h - g h) < 1) :
    f = g := by sorry
