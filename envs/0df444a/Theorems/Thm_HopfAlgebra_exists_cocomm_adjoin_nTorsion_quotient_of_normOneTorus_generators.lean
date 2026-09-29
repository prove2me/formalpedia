-- Prove2me | Theorems.Thm_HopfAlgebra_exists_cocomm_adjoin_nTorsion_quotient_of_normOneTorus_generators
-- name    : HopfAlgebra.exists_cocomm_adjoin_nTorsion_quotient_of_normOneTorus_generators
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/a246c380-3609-51e2-ac4e-7fa36df39b13
-- title:
--   n-torsion quotient of the norm-one torus, generated form
-- statement:
--   Let $K$ be a field of characteristic zero, let $c \in K$ be nonzero and not a square, let $n$ be a prime, and let $\delta$ be an element of the algebraic closure $\overline K$ with $\delta^2 = c$. Let $B$ be a commutative $K$-Hopf algebra containing elements $u, v$ with $u^2 - c\,v^2 = 1$, whose comultiplication satisfies $\Delta u = u \otimes u + c\,(v \otimes v)$ and $\Delta v = u \otimes v + v \otimes u$, and suppose that for every pair $(w,z)$ of elements of $\overline K$ with $w^2 - c\,z^2 = 1$ there is exactly one $K$-algebra homomorphism $B \to \overline K$ sending $u \mapsto w$ and $v \mapsto z$. The conclusion asserts the existence of a commutative ring $A$ carrying a $K$-Hopf algebra structure whose comultiplication is cocommutative, together with elements $u', v' \in A$ such that: $u'$ and $v'$ generate $A$ as a $K$-algebra, i.e. $\mathrm{adjoin}_K\{u',v'\} = \top$; $u'^2 - c\,v'^2 = 1$; $\Delta u' = u' \otimes u' + c\,(v' \otimes v')$ and $\Delta v' = u' \otimes v' + v' \otimes u'$; every $K$-algebra homomorphism $f : A \to \overline K$ satisfies $(f(u') + f(v')\delta)^n = 1$; and for every pair $(w,z)$ in $\overline K$ with $w^2 - c\,z^2 = 1$ and $(w + z\delta)^n = 1$ there is exactly one $K$-algebra homomorphism $A \to \overline K$ sending $u' \mapsto w$ and $v' \mapsto z$.
--
--   The Hopf algebra $A$ is the coordinate ring of the $n$-torsion subgroup scheme $T[n]$ of the norm-one torus $T$ of the quadratic extension $K(\sqrt c)/K$, presented so that the two given generators cut out the torus relation and the functor of points of $A$ over $\overline K$ is exactly the $n$-torsion of $T(\overline K)$. It is used to produce a finite flat group scheme of $n$-torsion type, being cited by [`HopfAlgebra.exists_finite_nTorsion_quotient_of_normOneTorus_generators`](thm.html#HopfAlgebra.exists_finite_nTorsion_quotient_of_normOneTorus_generators), where the generation condition $\mathrm{adjoin}_K\{u',v'\} = \top$ is converted into finiteness of $A$ over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_cocomm_adjoin_nTorsion_quotient_of_normOneTorus_generators.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.exists_cocomm_adjoin_nTorsion_quotient_of_normOneTorus_generators
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (B : Type) [CommRing B] [HopfAlgebra K B] (u v : B)
    (hrel : u ^ 2 - algebraMap K B c * v ^ 2 = 1)
    (hcu : Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v))
    (hcv : Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u)
    (hliftB : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! f : B →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Coalgebra.IsCocomm K A ∧
      ∃ (u' v' : A),
        (Algebra.adjoin K {u', v'} = ⊤) ∧
        (u' ^ 2 - algebraMap K A c * v' ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u' = u' ⊗ₜ[K] u' + c • (v' ⊗ₜ[K] v')) ∧
        (Coalgebra.comul (R := K) v' = u' ⊗ₜ[K] v' + v' ⊗ₜ[K] u') ∧
        (∀ f : A →ₐ[K] AlgebraicClosure K, (f u' + f v' * δ) ^ n = 1) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          (w + z * δ) ^ n = 1 →
          ∃! f : A →ₐ[K] AlgebraicClosure K, f u' = w ∧ f v' = z) := by sorry
