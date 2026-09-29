-- Prove2me | Theorems.Thm_LinearMap_trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two
-- name    : LinearMap.trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/ddde05b6-96dd-5fc2-896f-566d31d48771
-- title:
--   Trace defect of a quadratic endomorphism in dimension two
-- statement:
--   Let $k$ be a field and $V$ a finite-dimensional $k$-vector space with $\operatorname{finrank}_k V = 2$, let $\Phi \colon V \to V$ be a $k$-linear endomorphism, and let $t, n \in k$ be scalars such that $\Phi \circ \Phi - t\,\Phi + n\,\mathrm{id}_V = 0$ in the ring of $k$-linear endomorphisms of $V$ (multiplication being composition, and $1$ the identity map). Then, writing $u = \operatorname{tr}_k(\Phi) - t$ for the difference between the trace of $\Phi$ and the scalar $t$, one has
--   $$u\bigl(u^{2} - (t^{2} - 4n)\bigr) = 0$$
--   in $k$. Equivalently, the trace of $\Phi$ either equals $t$ or differs from it by a square root of the discriminant $t^{2} - 4n$ of the quadratic relation satisfied by $\Phi$. No hypothesis is imposed on the characteristic of $k$, and no separability or algebraic closedness is assumed.
--
--   This is the Cayley–Hamilton constraint on the trace of a two-dimensional representation of a quadratic relation: an endomorphism of a plane annihilated by $X^2 - tX + n$ has trace $t$ unless it is a scalar, in which case the trace defect is a square root of the discriminant. It is used in the study of polarised abelian schemes with quaternionic multiplication, where it shows that the locus where the trace on a two-dimensional Lie space differs from the reduced trace of the acting element is cut out by equations, so that the special and non-special loci are complementary zero sets; it is cited by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_opens_isClosed_range_subset_iff_trace`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_opens_isClosed_range_subset_iff_trace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 2) (Φ : V →ₗ[k] V) (t n : k) (hΦ : Φ * Φ - t • Φ + n • (1 : V →ₗ[k] V) = 0) :
    (LinearMap.trace k V Φ - t) * ((LinearMap.trace k V Φ - t) ^ 2 - (t ^ 2 - 4 * n)) = 0 := by sorry
