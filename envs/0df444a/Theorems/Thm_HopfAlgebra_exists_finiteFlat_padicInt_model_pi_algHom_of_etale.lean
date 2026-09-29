-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_model_pi_algHom_of_etale
-- name    : HopfAlgebra.exists_finiteFlat_padicInt_model_pi_algHom_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/83d90405-9825-5864-8516-2b2a466860ba
-- title:
--   Finite flat model for the induced module along an étale algebra
-- statement:
--   Let $p$ be a prime and let $G$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$ which is finite and flat as a $\mathbb{Z}_p$-module and whose comultiplication is cocommutative. Let $M$ be an additive commutative group equipped with a distributive multiplicative action of the group $\mathrm{Aut}_{\mathbb{Q}_p\text{-alg}}(\overline{\mathbb{Q}}_p)$ of $\mathbb{Q}_p$-algebra automorphisms of the algebraic closure `PadicAlgCl p` of $\mathbb{Q}_p$, and suppose given a bijection $e$ from the set $\mathrm{Hom}_{\mathbb{Z}_p\text{-alg}}(G,\overline{\mathbb{Q}}_p)$, regarded as a monoid under convolution (`WithConv`), onto $M$ such that $e(f\ast g)=e(f)+e(g)$, and such that whenever $g=\sigma\circ f$ pointwise for an automorphism $\sigma$ one has $e(g)=\sigma\cdot e(f)$. Let $B$ be a commutative $\mathbb{Z}_p$-algebra which is finite and free as a $\mathbb{Z}_p$-module and étale over $\mathbb{Z}_p$. Then there exists a commutative ring $H$ with a Hopf algebra structure over $\mathbb{Z}_p$, finite and flat as a $\mathbb{Z}_p$-module and cocommutative, together with a bijection $e'$ from $\mathrm{Hom}_{\mathbb{Z}_p\text{-alg}}(H,\overline{\mathbb{Q}}_p)$ under convolution onto the set of maps $\mathrm{Hom}_{\mathbb{Z}_p\text{-alg}}(B,\overline{\mathbb{Q}}_p)\to M$, satisfying $e'(f\ast g)=e'(f)+e'(g)$ and the twisted equivariance: if $g=\sigma\circ f$ pointwise, then for every $\tau\colon B\to\overline{\mathbb{Q}}_p$ one has $e'(g)(\sigma\circ\tau)=\sigma\cdot\bigl(e'(f)(\tau)\bigr)$, where $\sigma\circ\tau$ denotes $\tau$ followed by $\sigma$ viewed as a $\mathbb{Z}_p$-algebra map.
--
--   This realises the induced (co-induced) Galois module $\mathrm{Map}(\mathrm{Hom}_{\mathbb{Z}_p}(B,\overline{\mathbb{Q}}_p),M)$ as the group of $\overline{\mathbb{Q}}_p$-points of a finite flat commutative $\mathbb{Z}_p$-group scheme, the Weil restriction along the finite étale algebra $B$ of the base change of $G$. It is used in the construction of locally flat deformation data, being cited by [`ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one`](thm.html#ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_padicInt_model_pi_algHom_of_etale.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_finiteFlat_padicInt_model_pi_algHom_of_etale
    (p : ℕ) [Fact p.Prime]
    (G : Type) [CommRing G] [HopfAlgebra ℤ_[p] G] [Module.Finite ℤ_[p] G] [Module.Flat ℤ_[p] G]
    [Coalgebra.IsCocomm ℤ_[p] G]
    {M : Type} [AddCommGroup M] [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M]
    (e : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    (B : Type) [CommRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] [Module.Free ℤ_[p] B]
    [Algebra.Etale ℤ_[p] B] :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e' : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ((B →ₐ[ℤ_[p]] PadicAlgCl p) → M),
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ x : H, g x = σ (f x)) →
            ∀ τ : B →ₐ[ℤ_[p]] PadicAlgCl p,
              e' g (((σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).restrictScalars ℤ_[p]).comp τ) = σ • (e' f τ) := by sorry
