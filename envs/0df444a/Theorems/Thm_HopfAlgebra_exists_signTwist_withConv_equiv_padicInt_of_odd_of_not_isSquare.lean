-- Prove2me | Theorems.Thm_HopfAlgebra_exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare
-- name    : HopfAlgebra.exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/060972df-e713-5109-a07d-35c61448a99b
-- title:
--   Sign-twisted form of a finite flat ℤₚ-Hopf algebra
-- statement:
--   Let $p$ be an odd prime, let $d \in \mathbb{Q}_p$ have norm $\|d\|=1$ and not be a square, and let $s$ in an algebraic closure $\overline{\mathbb{Q}_p}$ satisfy $s^2 = d$ (the image of $d$ under the structure map). Let $H$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$ which is finite and flat as a $\mathbb{Z}_p$-module and whose comultiplication is cocommutative. Let $M$ be an additive abelian group equipped with a distributive multiplicative action of the group $\overline{\mathbb{Q}_p} \simeq_{\mathrm{alg}[\mathbb{Q}_p]} \overline{\mathbb{Q}_p}$ of $\mathbb{Q}_p$-algebra automorphisms of $\overline{\mathbb{Q}_p}$, and let $e$ be a bijection from the convolution monoid `WithConv` on the $\mathbb{Z}_p$-algebra maps $H \to \overline{\mathbb{Q}_p}$ onto $M$ such that $e(f\ast g) = e(f) + e(g)$ for all $f, g$, and such that whenever $g(h) = \sigma(f(h))$ for all $h \in H$ one has $e(g) = \sigma \cdot e(f)$. The conclusion asserts the existence of a type $H'$ with a commutative ring structure and a $\mathbb{Z}_p$-Hopf algebra structure, finite and flat over $\mathbb{Z}_p$ and cocommutative, together with a bijection $e'$ from the convolution monoid on the $\mathbb{Z}_p$-algebra maps $H' \to \overline{\mathbb{Q}_p}$ onto the same $M$, again satisfying $e'(f\ast g) = e'(f) + e'(g)$, and such that for every $\sigma$ and every pair $f, g$ with $g(h') = \sigma(f(h'))$ for all $h' \in H'$ one has $e'(g) = \sigma \cdot e'(f)$ if $\sigma(s) = s$ and $e'(g) = -(\sigma \cdot e'(f))$ if $\sigma(s) \neq s$.
--
--   This is the transport, along an identification of $\overline{\mathbb{Q}_p}$-points with an abstract Galois module $M$, of the quadratic étale twist of a finite flat cocommutative $\mathbb{Z}_p$-Hopf algebra by the unramified quadratic character attached to $\mathbb{Q}_p(\sqrt{d})$: the twisted Hopf algebra has the same points, but the Galois equivariance acquires the sign of that character. It is used in the construction of a finite flat prolongation of the torsion of a Weierstrass curve over $\mathbb{Z}_p$ whose points are only sign-twist equivariantly identified with the given module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal

theorem HopfAlgebra.exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1) (hd_nsq : ¬ IsSquare d)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hfin : Module.Finite ℤ_[p] H) (hflat : Module.Flat ℤ_[p] H)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H)
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ h : H, g h = σ (f h)) → e g = σ • (e f)) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra ℤ_[p] H'),
      Module.Finite ℤ_[p] H' ∧ Module.Flat ℤ_[p] H' ∧ Coalgebra.IsCocomm ℤ_[p] H' ∧
      ∃ e' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h' : H', g h' = σ (f h')) →
            (σ s = s → e' g = σ • (e' f)) ∧
            (σ s ≠ s → e' g = -(σ • (e' f))) := by sorry
