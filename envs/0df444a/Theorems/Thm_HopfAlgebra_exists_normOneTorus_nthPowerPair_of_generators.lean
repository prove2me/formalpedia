-- Prove2me | Theorems.Thm_HopfAlgebra_exists_normOneTorus_nthPowerPair_of_generators
-- name    : HopfAlgebra.exists_normOneTorus_nthPowerPair_of_generators
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/b23c57b1-e4c2-5336-b04d-58b6337a874d
-- title:
--   The n-th power pair on a norm-one torus Hopf algebra
-- statement:
--   Let $K$ be a field of characteristic zero, $c \in K$ with $c \neq 0$ and $c$ not a square in $K$, let $n$ be a prime, and let $\delta$ be an element of an algebraic closure $\overline{K}$ of $K$ with $\delta^2$ equal to the image of $c$. Let $B_0$ be a commutative ring carrying the structure of a $K$-Hopf algebra whose comultiplication is cocommutative, and let $u_0, v_0 \in B_0$ be elements generating $B_0$ as a $K$-algebra (i.e. $K[u_0,v_0] = \top$) and satisfying $u_0^2 - c\,v_0^2 = 1$, $\Delta(u_0) = u_0 \otimes u_0 + c\,(v_0 \otimes v_0)$ and $\Delta(v_0) = u_0 \otimes v_0 + v_0 \otimes u_0$, and assume that for every pair $(w,z)$ of elements of $\overline{K}$ with $w^2 - cz^2 = 1$ there is a unique $K$-algebra homomorphism $g : B_0 \to \overline{K}$ with $g(u_0) = w$ and $g(v_0) = z$. The conclusion asserts the existence of $P, Q \in B_0$ with $P^2 - c\,Q^2 = 1$, $\Delta(P) = P \otimes P + c\,(Q \otimes Q)$, $\Delta(Q) = P \otimes Q + Q \otimes P$, $\varepsilon(P) = 1$, $\varepsilon(Q) = 0$, and such that every $K$-algebra homomorphism $f : B_0 \to \overline{K}$ satisfies $f(P) + f(Q)\delta = (f(u_0) + f(v_0)\delta)^n$ and $f(P) - f(Q)\delta = (f(u_0) - f(v_0)\delta)^n$.
--
--   This is the polynomial half of the construction of the $n$-th power map on the norm-one torus $\mathrm{Res}^{(1)}_{K(\sqrt{c})/K}\mathbb{G}_m$ at the level of its coordinate Hopf algebra: the coordinates $(P,Q)$ of $(u_0,v_0)^n$ again satisfy the norm-one relation and the same comultiplication and counit formulas. It is used by [`HopfAlgebra.exists_cocomm_adjoin_nTorsion_quotient_of_adjoin_normOneTorus`](thm.html#HopfAlgebra.exists_cocomm_adjoin_nTorsion_quotient_of_adjoin_normOneTorus), which passes to the $n$-torsion quotient of such a torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_normOneTorus_nthPowerPair_of_generators.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.exists_normOneTorus_nthPowerPair_of_generators
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (B₀ : Type) [CommRing B₀] [HopfAlgebra K B₀] (hcc₀ : Coalgebra.IsCocomm K B₀)
    (u₀ v₀ : B₀)
    (hgen₀ : Algebra.adjoin K {u₀, v₀} = ⊤)
    (hrel₀ : u₀ ^ 2 - algebraMap K B₀ c * v₀ ^ 2 = 1)
    (hcu₀ : Coalgebra.comul (R := K) u₀ = u₀ ⊗ₜ[K] u₀ + c • (v₀ ⊗ₜ[K] v₀))
    (hcv₀ : Coalgebra.comul (R := K) v₀ = u₀ ⊗ₜ[K] v₀ + v₀ ⊗ₜ[K] u₀)
    (hlift₀ : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! g : B₀ →ₐ[K] AlgebraicClosure K, g u₀ = w ∧ g v₀ = z) :
    ∃ (P Q : B₀),
      (P ^ 2 - algebraMap K B₀ c * Q ^ 2 = 1) ∧
      (Coalgebra.comul (R := K) P = P ⊗ₜ[K] P + c • (Q ⊗ₜ[K] Q)) ∧
      (Coalgebra.comul (R := K) Q = P ⊗ₜ[K] Q + Q ⊗ₜ[K] P) ∧
      (Coalgebra.counit (R := K) P = 1) ∧
      (Coalgebra.counit (R := K) Q = 0) ∧
      (∀ f : B₀ →ₐ[K] AlgebraicClosure K,
        f P + f Q * δ = (f u₀ + f v₀ * δ) ^ n ∧
        f P - f Q * δ = (f u₀ - f v₀ * δ) ^ n) := by sorry
