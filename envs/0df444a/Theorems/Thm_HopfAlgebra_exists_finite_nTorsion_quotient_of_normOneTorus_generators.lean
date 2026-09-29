-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finite_nTorsion_quotient_of_normOneTorus_generators
-- name    : HopfAlgebra.exists_finite_nTorsion_quotient_of_normOneTorus_generators
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/a3ebac4f-78f7-5c29-81e3-171cad48a4f0
-- title:
--   Finite cocommutative n-torsion quotient of a norm-one torus
-- statement:
--   Let $K$ be a field of characteristic zero, $c \in K$ with $c \neq 0$ and $c$ not a square in $K$, let $n$ be a prime, and let $\delta$ be an element of the algebraic closure $\overline{K}$ with $\delta^2 = c$ (the image of $c$ under the structure map). Let $B$ be a commutative $K$-Hopf algebra containing elements $u, v$ with $u^2 - c v^2 = 1$ and with comultiplication $\Delta(u) = u \otimes u + c\,(v \otimes v)$, $\Delta(v) = u \otimes v + v \otimes u$, and assume that for every pair $(w,z)$ of elements of $\overline{K}$ with $w^2 - c z^2 = 1$ there is exactly one $K$-algebra homomorphism $B \to \overline{K}$ sending $u \mapsto w$ and $v \mapsto z$. The conclusion asserts the existence of a commutative ring $A$ carrying a $K$-Hopf algebra structure which is finite as a $K$-module and whose comultiplication is cocommutative, together with elements $u', v' \in A$ satisfying the same relation $u'^2 - c v'^2 = 1$ and the same two comultiplication formulae, such that every $K$-algebra homomorphism $f : A \to \overline{K}$ satisfies $(f(u') + f(v')\delta)^n = 1$, and such that for every $(w,z)$ in $\overline{K}$ with $w^2 - c z^2 = 1$ and $(w + z\delta)^n = 1$ there is exactly one $K$-algebra homomorphism $A \to \overline{K}$ with $u' \mapsto w$ and $v' \mapsto z$.
--
--   This is the Hopf-algebraic form of the statement that the $n$-torsion subgroup scheme of the norm-one torus of the quadratic extension $K(\sqrt{c})/K$ is a finite group scheme over $K$, presented by the same pair of coordinate functions and with commutative (hence cocommutative coordinate) group law. It feeds the construction of finite flat group schemes used in the local study of Galois representations, being cited by [`HopfAlgebra.exists_finite_cocomm_generated_normOneTorusNTorsion`](thm.html#HopfAlgebra.exists_finite_cocomm_generated_normOneTorusNTorsion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finite_nTorsion_quotient_of_normOneTorus_generators.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.exists_finite_nTorsion_quotient_of_normOneTorus_generators
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
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ (u' v' : A),
        (u' ^ 2 - algebraMap K A c * v' ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u' = u' ⊗ₜ[K] u' + c • (v' ⊗ₜ[K] v')) ∧
        (Coalgebra.comul (R := K) v' = u' ⊗ₜ[K] v' + v' ⊗ₜ[K] u') ∧
        (∀ f : A →ₐ[K] AlgebraicClosure K, (f u' + f v' * δ) ^ n = 1) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          (w + z * δ) ^ n = 1 →
          ∃! f : A →ₐ[K] AlgebraicClosure K, f u' = w ∧ f v' = z) := by sorry
