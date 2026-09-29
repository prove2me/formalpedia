-- Prove2me | Theorems.Thm_HopfAlgebra_exists_cocomm_normOneTorus_generators_and_points
-- name    : HopfAlgebra.exists_cocomm_normOneTorus_generators_and_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/f849fb9e-e149-56c0-8bc9-e121d6622488
-- title:
--   Explicit cocommutative Hopf algebra of the norm-one torus
-- statement:
--   Let $K$ be a field of characteristic zero, let $c \in K$ be non-zero and not a square in $K$, let $n$ be a prime natural number, and let $\delta$ be an element of the algebraic closure $\overline{K}$ with $\delta^2$ equal to the image of $c$ under the structure map $K \to \overline{K}$. The assertion is that there exist a type $B$ carrying a commutative ring structure and a $K$-Hopf algebra structure such that the comultiplication of $B$ is cocommutative (in the sense of `Coalgebra.IsCocomm`, i.e. composing $\Delta$ with the flip of $B \otimes_K B$ returns $\Delta$), together with two elements $u, v \in B$ satisfying the relation $u^2 - c\,v^2 = 1$ (with $c$ acting through $K \to B$), the comultiplication formulas $\Delta(u) = u \otimes u + c\,(v \otimes v)$ and $\Delta(v) = u \otimes v + v \otimes u$, and the following point-counting property: for every pair $(w, z)$ of elements of $\overline{K}$ with $w^2 - c z^2 = 1$ there is a unique $K$-algebra homomorphism $f \colon B \to \overline{K}$ with $f(u) = w$ and $f(v) = z$. No further conditions (such as finite generation, or a description of the counit and antipode) are asserted.
--
--   This realises the coordinate ring of the norm-one torus $\mathrm{Res}^{(1)}_{K(\sqrt{c})/K}\mathbb{G}_m$, namely $K[U,V]/(U^2 - cV^2 - 1)$ with the Hopf structure encoding the group law $(u_1,v_1)(u_2,v_2) = (u_1u_2 + cv_1v_2,\, u_1v_2 + v_1u_2)$, the final clause identifying the $\overline{K}$-points of $\operatorname{Spec} B$ with the norm-one elements. It is used by [`HopfAlgebra.exists_finite_cocomm_generated_normOneTorusNTorsion`](thm.html#HopfAlgebra.exists_finite_cocomm_generated_normOneTorusNTorsion) in the treatment of finite flat group schemes attached to Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_cocomm_normOneTorus_generators_and_points.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.exists_cocomm_normOneTorus_generators_and_points
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c) :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra K B),
      Coalgebra.IsCocomm K B ∧
      ∃ (u v : B),
        (u ^ 2 - algebraMap K B c * v ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v)) ∧
        (Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          ∃! f : B →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) := by sorry
