-- Prove2me | Theorems.Thm_HopfAlgebra_exists_signTwist_withConv_mulEquiv_padicInt_of_odd_of_not_isSquare
-- name    : HopfAlgebra.exists_signTwist_withConv_mulEquiv_padicInt_of_odd_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/5322c1c7-3d1c-5727-8449-3843d5976d87
-- title:
--   Quadratic twist of a finite flat cocommutative ℤₚ-Hopf algebra
-- statement:
--   Let $p$ be an odd prime, let $d \in \mathbb{Q}_p$ have $p$-adic norm $\lVert d\rVert = 1$ and not be a square in $\mathbb{Q}_p$, and let $s$ be an element of $\mathrm{AlgebraicClosure}\,\mathbb{Q}_p$ with $s^2$ equal to the image of $d$. Let $H$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$ which is finite and flat as a $\mathbb{Z}_p$-module and whose comultiplication is cocommutative. The assertion is that there exists a type $H'$, again a commutative ring with a $\mathbb{Z}_p$-Hopf algebra structure, finite and flat over $\mathbb{Z}_p$ and cocommutative, together with a bijection $\beta$ from $\mathrm{WithConv}(H' \to_{\mathrm{alg}[\mathbb{Z}_p]} \mathrm{AlgebraicClosure}\,\mathbb{Q}_p)$ onto $\mathrm{WithConv}(H \to_{\mathrm{alg}[\mathbb{Z}_p]} \mathrm{AlgebraicClosure}\,\mathbb{Q}_p)$, i.e. a bijection on $\overline{\mathbb{Q}}_p$-points, such that: (i) $\beta(f' g') = \beta(f')\,\beta(g')$ for all points $f', g'$ of $H'$, the products being convolution; and (ii) for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\mathrm{AlgebraicClosure}\,\mathbb{Q}_p$, all points $f', g'$ of $H'$ and every point $g$ of $H$ satisfying $g'(h') = \sigma(f'(h'))$ for all $h' \in H'$ and $g(h) = \sigma((\beta f')(h))$ for all $h \in H$, one has $\beta(g') = g$ whenever $\sigma(s) = s$, and $\beta(g')\,g = 1$ in the convolution monoid whenever $\sigma(s) \neq s$. Multiplicativity of $\beta$ is recorded as a separate clause rather than packaged into the equivalence.
--
--   This is the quadratic twist by $d$ of a finite flat cocommutative commutative Hopf algebra over $\mathbb{Z}_p$, stated at the level of $\overline{\mathbb{Q}}_p$-points: the twisted Hopf algebra has the same point group, but the Galois action is altered by the quadratic character attached to $\mathbb{Q}_p(\sqrt{d})$, inversion occurring exactly for those $\sigma$ moving $s$. It is used in the analysis of finite flat group schemes attached to $p$-adic Galois representations, and feeds the companion statement [`HopfAlgebra.exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare`](thm.html#HopfAlgebra.exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_signTwist_withConv_mulEquiv_padicInt_of_odd_of_not_isSquare.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal

theorem HopfAlgebra.exists_signTwist_withConv_mulEquiv_padicInt_of_odd_of_not_isSquare
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1) (hd_nsq : ¬ IsSquare d)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hfin : Module.Finite ℤ_[p] H) (hflat : Module.Flat ℤ_[p] H)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra ℤ_[p] H'),
      Module.Finite ℤ_[p] H' ∧ Module.Flat ℤ_[p] H' ∧ Coalgebra.IsCocomm ℤ_[p] H' ∧
      ∃ β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
            WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ f' g', β (f' * g') = β f' * β g') ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f' g' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
          (g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h' : H', g' h' = σ (f' h')) →
          (∀ h : H, g h = σ ((β f') h)) →
            (σ s = s → β g' = g) ∧ (σ s ≠ s → β g' * g = 1) := by sorry
