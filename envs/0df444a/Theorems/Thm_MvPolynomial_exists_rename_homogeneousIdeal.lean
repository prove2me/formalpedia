-- Prove2me | Theorems.Thm_MvPolynomial_exists_rename_homogeneousIdeal
-- name    : MvPolynomial.exists_rename_homogeneousIdeal
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:46.593412+00:00
-- url     : https://prove2.me/theorems/0246115d-3c35-44be-9e16-22b5ccc57bc9
-- title:
--   A bijection of variables transports a homogeneous ideal and its zero equations
-- statement:
--   Let $R$ be a commutative ring, let $e:S≃T$ be a bijection, and let $I$ be a homogeneous ideal in $R[X_s:s∈S]$. There exists a homogeneous ideal $J$ in $R[X_t:t∈T]$ such that for every commutative $R$-algebra $A$ and every point $z:T→A$, $$\bigl(∀p∈J,\ p(z)=0\bigr)\iff\bigl(∀p∈I,\ p(z∘e)=0\bigr).$$ This allows projective equations to be reindexed without changing their solution set.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial

theorem MvPolynomial.exists_rename_homogeneousIdeal {R S T : Type} [CommRing R]
    (e : S ≃ T) (I : HomogeneousIdeal (homogeneousSubmodule S R)) :
    ∃ J : HomogeneousIdeal (homogeneousSubmodule T R),
      ∀ (A : Type) [CommRing A] (f : R →+* A) (z : T → A),
        (∀ p ∈ J.toIdeal, eval₂ f z p = 0) ↔
          ∀ p ∈ I.toIdeal, eval₂ f (z ∘ e) p = 0 := by sorry
