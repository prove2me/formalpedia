-- Prove2me | Theorems.Thm_HopfAlgebra_exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt
-- name    : HopfAlgebra.exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/57de3f4e-6938-509f-818e-cee33ec4a65d
-- title:
--   Sign-twisted point bijection for a d₀-twisted p-adic Hopf algebra
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $d \in \mathbb{Q}_p$ satisfy $\|d\|=1$ and not be a square, let $s$ be an element of $\overline{\mathbb{Q}_p} =$ `AlgebraicClosure ℚ_[p]` with $s^2$ equal to the image of $d$, and let $d_0 \in \mathbb{Z}_p$ be a unit whose image in $\mathbb{Q}_p$ is $d$. Let $H$ and $H'$ be commutative rings carrying $\mathbb{Z}_p$-Hopf algebra structures, each finite and flat as a $\mathbb{Z}_p$-module and cocommutative as a coalgebra, and let $e : H' \to H$ be a $\mathbb{Z}_p$-linear isomorphism with $e(1) = 1$. Writing $P_- = \tfrac{1}{2}(\mathrm{id} - \iota)$ for the endomorphism of $H$ built from the inverse of $2$ in $\mathbb{Z}_p$ and the antipode $\iota$, assume that $e$ transports the structure maps of $H'$ in the explicitly $d_0$-twisted way: $e(ab) = e(a)e(b) + (d_0 - 1)\,P_-(e(a))P_-(e(b))$ for all $a, b \in H'$; the counit of $e(a)$ equals that of $a$; $e$ commutes with the antipodes; and $(e \otimes e)(\Delta a) = \Delta(e(a)) + (d_0^{-1} - 1)\,(P_- \otimes P_-)(\Delta(e(a)))$ for all $a \in H'$. Then there is a bijection $\beta$ from the set of $\mathbb{Z}_p$-algebra homomorphisms $H' \to \overline{\mathbb{Q}_p}$ to the set of $\mathbb{Z}_p$-algebra homomorphisms $H \to \overline{\mathbb{Q}_p}$, each set equipped via `WithConv` with its convolution product, such that $\beta(f'g') = \beta(f')\,\beta(g')$ for all $f', g'$, and such that for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}_p}$ and all points $f', g'$ of $H'$ and $g$ of $H$ with $g'(h') = \sigma(f'(h'))$ for all $h' \in H'$ and $g(h) = \sigma((\beta f')(h))$ for all $h \in H$: if $\sigma s = s$ then $\beta(g') = g$, and if $\sigma s \neq s$ then $\beta(g')\,g = 1$ in the convolution monoid.
--
--   This is the point-bijection half of the quadratic (sign) twist comparison for finite flat cocommutative Hopf algebras over $\mathbb{Z}_p$: the $\overline{\mathbb{Q}_p}$-points of the twisted Hopf algebra $H'$ are identified with those of $H$ by a group isomorphism which is equivariant for the Galois action up to the quadratic character cut out by $s^2 = d$. It feeds [`HopfAlgebra.exists_signTwist_withConv_mulEquiv_padicInt_of_odd_of_not_isSquare`](thm.html#HopfAlgebra.exists_signTwist_withConv_mulEquiv_padicInt_of_odd_of_not_isSquare), where the twisted Hopf algebra $H'$ and the $d_0$-twisted structure identities are produced rather than assumed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped TensorProduct in

theorem HopfAlgebra.exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1) (hd_nsq : ¬ IsSquare d)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (d₀ : ℤ_[p]) (hd₀d : (d₀ : ℚ_[p]) = d) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hfin : Module.Finite ℤ_[p] H) (hflat : Module.Flat ℤ_[p] H)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H)
    (H' : Type) [CommRing H'] [HopfAlgebra ℤ_[p] H']
    (hfin' : Module.Finite ℤ_[p] H') (hflat' : Module.Flat ℤ_[p] H')
    (hcocomm' : Coalgebra.IsCocomm ℤ_[p] H')
    (e : H' ≃ₗ[ℤ_[p]] H)
    (he1 : e 1 = 1)
    (hemul : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ a b : H', e (a * b) = e a * e b + (d₀ - 1) • (Pm (e a) * Pm (e b)))
    (hecounit : ∀ a : H', (Coalgebra.counit (e a) : ℤ_[p]) = Coalgebra.counit a)
    (heant : ∀ a : H', e (HopfAlgebra.antipode ℤ_[p] a) = HopfAlgebra.antipode ℤ_[p] (e a))
    (hecomul : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ a : H', (TensorProduct.map (e : H' →ₗ[ℤ_[p]] H) (e : H' →ₗ[ℤ_[p]] H))
                  (Coalgebra.comul a)
            = Coalgebra.comul (e a)
              + (Ring.inverse d₀ - 1) •
                  (TensorProduct.map Pm Pm) (Coalgebra.comul (e a))) :
    ∃ β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
      (∀ f' g', β (f' * g') = β f' * β g') ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (f' g' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
        (g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
        (∀ h' : H', g' h' = σ (f' h')) →
        (∀ h : H, g h = σ ((β f') h)) →
          (σ s = s → β g' = g) ∧ (σ s ≠ s → β g' * g = 1) := by sorry
