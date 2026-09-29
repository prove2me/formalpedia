-- Prove2me | Theorems.Thm_ModularCurve_finiteFlatModel_heckeEndo_one_mul_add
-- name    : ModularCurve.finiteFlatModel_heckeEndo_one_mul_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/27b5b420-9ea0-51a0-bdd4-70cdde2075bd
-- title:
--   Hecke action on a finite flat model: unit, composition, convolution
-- statement:
--   Fix $N$ with $N \neq 0$, a prime $p$, and an ideal $\mathfrak m$ of $\mathbb T =$ `HeckeAlg`, the polynomial ring $\mathbb Z[X_\ell : \ell \text{ prime}]$ over $\mathbb Z$ in variables indexed by the primes. Write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$ (that is, $\mathbb Z_{(p)}$), and let `JZero N` be the degree-zero divisor class group $\mathrm{Pic}^0$ of the function field `modularFunctionFieldBar N` over $\overline{\mathbb Q}$, equipped with the $\mathbb T$-module structure `heckeModuleBar N` (evaluation of the polynomial variables at the Hecke operators when these commute, and the trivial structure otherwise); `heckeTorsion (JZero N) 𝔪` is the submodule of elements annihilated by every element of $\mathfrak m$. Let $H$ be a commutative ring that is a Hopf algebra over $R$, finite and flat as an $R$-module, and let `WithConv (H →ₐ[R] AlgebraicClosure ℚ)` be the set of $R$-algebra homomorphisms $H \to \overline{\mathbb Q}$ with the convolution product coming from the Hopf structure. Assume given a bijection $e$ from this set of points onto `heckeTorsion (JZero N) 𝔪` that is additive in the sense $e(f \cdot g) = e(f) + e(g)$, together with a function $\varphi$ from $\mathbb T$ to the $R$-algebra endomorphisms of $H$ such that for all $t \in \mathbb T$ and all points $f, g$ with $g(h) = f(\varphi(t)(h))$ for every $h \in H$, the images of $e(g)$ and $t \cdot e(f)$ in `JZero N` agree. Then, for all $t_1, t_2 \in \mathbb T$: $\varphi(1)$ is the identity algebra endomorphism of $H$; $\varphi(t_1 t_2) = \varphi(t_1) \circ \varphi(t_2)$; and the $R$-linear map underlying $\varphi(t_1 + t_2)$ equals the composite of the comultiplication of $H$, the tensor product map $\varphi(t_1) \otimes \varphi(t_2)$, and the multiplication $H \otimes_R H \to H$, i.e. $\varphi(t_1 + t_2)$ is the convolution of $\varphi(t_1)$ and $\varphi(t_2)$.
--
--   This records that the endomorphisms $\varphi(t)$ transporting the Hecke action along a finite flat $\mathbb Z_{(p)}$-model $H$ of the $\mathfrak m$-torsion of the Jacobian constitute an action of the ring $\mathbb T$ by endomorphisms of the associated group scheme: unital and multiplicative for composition, and additive for the convolution product. It feeds the bound on the rank of `heckeTorsion (JZero N) 𝔪` used in the multiplicity-one step, via [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteFlatModel_heckeEndo_one_mul_add.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in
open scoped TensorProduct in

theorem ModularCurve.finiteFlatModel_heckeEndo_one_mul_add
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (e : letI := heckeModuleBar N
      WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥(heckeTorsion (JZero N) 𝔪))
    (he_add : letI := heckeModuleBar N
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), e (f * g) = e f + e g)
    (φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = f (φ t h)) → ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = t • ((e f : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N))
    (t₁ t₂ : HeckeAlg) :
    φ 1 = AlgHom.id (GaloisRep.ratLocalizedAt p) H ∧
      φ (t₁ * t₂) = (φ t₁).comp (φ t₂) ∧
      (φ (t₁ + t₂)).toLinearMap =
        LinearMap.mul' (GaloisRep.ratLocalizedAt p) H ∘ₗ
          TensorProduct.map (φ t₁).toLinearMap (φ t₂).toLinearMap ∘ₗ
            Coalgebra.comul (R := GaloisRep.ratLocalizedAt p) (A := H) := by sorry
