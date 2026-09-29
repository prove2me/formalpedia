-- Prove2me | Theorems.Thm_HopfAlgebra_normOneTorus_quotient_nTorsion_points_of_powerPair
-- name    : HopfAlgebra.normOneTorus_quotient_nTorsion_points_of_powerPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/2e94440b-be66-5d3b-952f-48dc1c42520f
-- title:
--   ̄ K-points of the n-torsion of the norm-one torus
-- statement:
--   Let $K$ be a field of characteristic zero, let $c \in K$ be nonzero, let $n$ be a prime, and let $\delta \in \overline K$ satisfy $\delta \cdot \delta = c$ (the image of $c$ under the structure map $K \to \overline K$). Let $B_0$ be a commutative $K$-algebra with elements $u_0, v_0, P, Q$ such that: (i) for every pair $(w,z)$ of elements of $\overline K$ with $w^2 - cz^2 = 1$ there is a unique $K$-algebra map $g : B_0 \to \overline K$ with $g(u_0) = w$ and $g(v_0) = z$; (ii) every $K$-algebra map $f : B_0 \to \overline K$ satisfies both $f(P) + f(Q)\delta = (f(u_0) + f(v_0)\delta)^n$ and $f(P) - f(Q)\delta = (f(u_0) - f(v_0)\delta)^n$. Let $A$ be a commutative $K$-algebra with elements $u', v'$ generating $A$ as a $K$-algebra, i.e. $\mathrm{adjoin}_K\{u',v'\} = \top$, and let $\pi : B_0 \to A$ be a $K$-algebra map with $\pi(u_0) = u'$, $\pi(v_0) = v'$, $\pi(P) = 1$, $\pi(Q) = 0$, such that every $K$-algebra map $g : B_0 \to \overline K$ with $g(P) = 1$ and $g(Q) = 0$ factors as $g = f \circ \pi$ for some $K$-algebra map $f : A \to \overline K$. The conclusion is twofold: every $K$-algebra map $f : A \to \overline K$ satisfies $(f(u') + f(v')\delta)^n = 1$; and for every pair $(w,z)$ in $\overline K$ with $w^2 - cz^2 = 1$ and $(w + z\delta)^n = 1$ there is a unique $K$-algebra map $f : A \to \overline K$ with $f(u') = w$ and $f(v') = z$.
--
--   This identifies the $\overline K$-points of $\operatorname{Spec} A$, presented as the quotient of the coordinate ring $B_0$ of the norm-one torus $w^2 - cz^2 = 1$ by the relations $P = 1$, $Q = 0$ cutting out the $n$-torsion, with the group of $n$-th roots of unity inside the torus: pairs $(w,z)$ satisfying $w^2 - cz^2 = 1$ and $(w+z\delta)^n = 1$. It is the points half of the construction of the $n$-torsion subscheme as a commutative Hopf algebra over $K$, used by [`HopfAlgebra.exists_cocomm_adjoin_nTorsion_quotient_of_powerPair`](thm.html#HopfAlgebra.exists_cocomm_adjoin_nTorsion_quotient_of_powerPair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_normOneTorus_quotient_nTorsion_points_of_powerPair.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.normOneTorus_quotient_nTorsion_points_of_powerPair
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (B₀ : Type) [CommRing B₀] [Algebra K B₀]
    (u₀ v₀ P Q : B₀)
    (hlift₀ : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! g : B₀ →ₐ[K] AlgebraicClosure K, g u₀ = w ∧ g v₀ = z)
    (hpow : ∀ f : B₀ →ₐ[K] AlgebraicClosure K,
      f P + f Q * δ = (f u₀ + f v₀ * δ) ^ n ∧
      f P - f Q * δ = (f u₀ - f v₀ * δ) ^ n)
    (A : Type) [CommRing A] [Algebra K A]
    (u' v' : A) (π : B₀ →ₐ[K] A)
    (hπu : π u₀ = u') (hπv : π v₀ = v') (hπP : π P = 1) (hπQ : π Q = 0)
    (hfact : ∀ g : B₀ →ₐ[K] AlgebraicClosure K, g P = 1 → g Q = 0 →
      ∃ f : A →ₐ[K] AlgebraicClosure K, f.comp π = g)
    (hgen' : Algebra.adjoin K {u', v'} = ⊤) :
    (∀ f : A →ₐ[K] AlgebraicClosure K, (f u' + f v' * δ) ^ n = 1) ∧
    (∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      (w + z * δ) ^ n = 1 →
      ∃! f : A →ₐ[K] AlgebraicClosure K, f u' = w ∧ f v' = z) := by sorry
