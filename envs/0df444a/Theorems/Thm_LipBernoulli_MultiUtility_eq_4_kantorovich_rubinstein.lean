-- Prove2me | Theorems.Thm_LipBernoulli_MultiUtility_eq_4_kantorovich_rubinstein
-- name    : LipBernoulli.MultiUtility.eq_4_kantorovich_rubinstein
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:14.247339+00:00
-- url     : https://prove2.me/theorems/2d436449-efd3-400c-8cdb-4285f18e5b91
-- title:
--   (4), p. 5 — Kantorovich–Rubinstein duality: W1(p, q) = sup |∫ f d(p − q)| over 1-Lipschitz f, on a separable metric space
-- statement:
--   Let $X$ be a separable metric space with its Borel $\sigma$-algebra and let $p, q \in \Delta_1(X)$. Then
--   $$
--   W_1(p,q) = \sup_{f}\ \Big|\int_X f\,\mathrm dp - \int_X f\,\mathrm dq\Big|,
--   $$
--   the supremum over all 1-Lipschitz functions $f : X \to \mathbb R$.
--
--   This is the Kantorovich–Rubinstein duality theorem, which the paper cites (unnumbered, display (4)) and uses to compute the KR norm of $\alpha(p-q)$ (Proposition 2.2) and to bound utility differences by $W_1$ in Proposition 4.2.
--
--   **Formalization Note** Both sides are valued in $[0,\infty]$: $W_1$ is the coupling infimum, and the supremum is of `ENNReal.ofReal` of the absolute values, so no real supremum over a possibly unbounded set is taken. The paper's $\int f\,\mathrm d(p-q)$ is written as $\int f\,\mathrm dp - \int f\,\mathrm dq$; both integrals are finite by Proposition 2.1.
-- source:
--   Ok & Weaver, Lipschitz Bernoulli Utility Functions, arXiv:2104.11205v1, (4), p. 5 (Kantorovich–Rubinstein duality theorem, cited)

import Mathlib
import Definitions.Def_LipBernoulli_MultiUtility_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace LipBernoulli.MultiUtility

/-- The Kantorovich–Rubinstein duality theorem, (4), p. 5: if `X` is separable then for any
`p, q ∈ Δ₁(X)`, `W₁(p, q) = sup |∫_X f d(p − q)|`, the supremum over all 1-Lipschitz `f`. -/
theorem eq_4_kantorovich_rubinstein {X : Type*} [MetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (p q : Measure X) (hp : p ∈ Delta1 X) (hq : q ∈ Delta1 X) :
    W1 p q = ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f),
      ENNReal.ofReal |∫ x, f x ∂p - ∫ x, f x ∂q| := by sorry

end LipBernoulli.MultiUtility
