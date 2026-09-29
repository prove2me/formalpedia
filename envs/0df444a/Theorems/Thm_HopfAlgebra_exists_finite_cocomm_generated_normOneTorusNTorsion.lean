-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finite_cocomm_generated_normOneTorusNTorsion
-- name    : HopfAlgebra.exists_finite_cocomm_generated_normOneTorusNTorsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/ceef33de-bb06-5b10-b8d9-7dd2c78eea66
-- title:
--   Finite cocommutative Hopf algebra for norm-one torus n-torsion
-- statement:
--   Let $K$ be a field of characteristic zero, let $c \in K$ be non-zero and not a square in $K$, let $n$ be a natural number that is prime (supplied as a `Fact` instance), and let $\delta$ be an element of the algebraic closure $\overline{K}$ with $\delta^2$ equal to the image of $c$ under the structure map $K \to \overline{K}$. The assertion is that there exist a type $A$ together with commutative ring and $K$-Hopf algebra structures on it such that $A$ is finite as a $K$-module, the comultiplication of $A$ is cocommutative, and there are elements $u, v \in A$ with: $u^2 - c\,v^2 = 1$ (where $c$ acts through $K \to A$); $\Delta(u) = u \otimes u + c \cdot (v \otimes v)$ and $\Delta(v) = u \otimes v + v \otimes u$ in $A \otimes_K A$; every $K$-algebra homomorphism $f \colon A \to \overline{K}$ satisfies $(f(u) + f(v)\delta)^n = 1$; and, conversely, for every pair $w, z \in \overline{K}$ with $w^2 - c z^2 = 1$ and $(w + z\delta)^n = 1$ there is exactly one $K$-algebra homomorphism $f \colon A \to \overline{K}$ with $f(u) = w$ and $f(v) = z$.
--
--   The algebra $A$ is the coordinate ring of the $n$-torsion subscheme of the norm-one torus of the quadratic extension $K(\sqrt{c})/K$, the last two clauses expressing that its $\overline{K}$-points are exactly the norm-one elements whose associated element $w + z\delta$ is an $n$-th root of unity. It feeds the comparison between $K$-algebra homomorphisms out of such a Hopf algebra and the $n$-th roots of unity in a quadratic twist, used in [`HopfAlgebra.exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist`](thm.html#HopfAlgebra.exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finite_cocomm_generated_normOneTorusNTorsion.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.exists_finite_cocomm_generated_normOneTorusNTorsion
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ (u v : A),
        (u ^ 2 - algebraMap K A c * v ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v)) ∧
        (Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u) ∧
        (∀ f : A →ₐ[K] AlgebraicClosure K, (f u + f v * δ) ^ n = 1) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          (w + z * δ) ^ n = 1 →
          ∃! f : A →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) := by sorry
