-- Prove2me | Theorems.Thm_LinearMap_trace_eq_and_det_eq_of_semiconj
-- name    : LinearMap.trace_eq_and_det_eq_of_semiconj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/91005b05-c874-54fd-86a7-c3a3a725813d
-- title:
--   Trace and determinant are invariant under semiconjugation
-- statement:
--   Let $R$ be a commutative ring and let $M$ and $N$ be $R$-modules (additive commutative groups with $R$-module structures). Let $e : M \simeq_R N$ be an $R$-linear isomorphism, let $f$ be an $R$-linear endomorphism of $M$ and $g$ an $R$-linear endomorphism of $N$, and suppose that $e$ intertwines them pointwise: $e(f(x)) = g(e(x))$ for every $x \in M$, i.e. $g = e \circ f \circ e^{-1}$. The conclusion is the conjunction of two equalities: the trace of $f$ as an endomorphism of $M$ equals the trace of $g$ as an endomorphism of $N$, and the determinant of $f$ equals the determinant of $g$. No finiteness or freeness hypothesis is imposed on $M$ or $N$; the trace and determinant are those of Mathlib, defined via a finite basis when one exists and by the default conventions ($0$ for the trace, $1$ for the determinant) otherwise, and the two modules are simultaneously finite free or not, so the equalities hold unconditionally.
--
--   This is the similarity invariance of trace and determinant, in the form needed to transport these invariants along an isomorphism between two different modules rather than within a single one. It is used by [`WeierstrassCurve.IsIntegralModelOf.galoisTrace_det_frobenius`](thm.html#WeierstrassCurve.IsIntegralModelOf.galoisTrace_det_frobenius) to carry the trace and determinant of a Frobenius element across a Galois-equivariant isomorphism of torsion modules arising from a change of model of an elliptic curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_trace_eq_and_det_eq_of_semiconj.lean

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LinearMap.trace_eq_and_det_eq_of_semiconj {R : Type*} {M : Type*} {N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (f : Module.End R M) (g : Module.End R N) (h : ∀ x : M, e (f x) = g (e x)) : LinearMap.trace R M f = LinearMap.trace R N g ∧ LinearMap.det f = LinearMap.det g := by sorry
