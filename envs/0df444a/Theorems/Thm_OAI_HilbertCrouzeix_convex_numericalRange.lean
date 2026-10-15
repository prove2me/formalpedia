-- Prove2me | Theorems.Thm_OAI_HilbertCrouzeix_convex_numericalRange
-- name    : OAI.HilbertCrouzeix.convex_numericalRange
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:04:03.638986+00:00
-- url     : https://prove2.me/theorems/70fc0f28-d421-42b1-b545-65c8ee884342
-- title:
--   The numerical range of a bounded operator is convex
-- statement:
--   Let $H$ be a complex inner product space, not necessarily complete, whose inner product $\langle\cdot,\cdot\rangle$ is conjugate-linear in the first argument and linear in the second, and let $A:H\to H$ be a bounded complex-linear operator. The numerical range of $A$ is the set of complex numbers
--   $$
--   W(A)=\{\langle x,Ax\rangle:\ x\in H,\ \|x\|=1\}\subseteq\mathbb{C}.
--   $$
--   The theorem asserts that $W(A)$ is convex when $\mathbb{C}$ is regarded as a real vector space: for all $z,w\in W(A)$ and all real numbers $a,b\ge0$ with $a+b=1$,
--   $$
--   az+bw\in W(A).
--   $$
--
--   No closure is taken: the numerical range itself is convex. When $H=\{0\}$ there are no unit vectors, $W(A)$ is empty, and the statement holds trivially.
--
--   Convexity passes to the closure $\overline{W(A)}$, the numerical closure, which is one of the three basic geometric properties (together with compactness and, for complete $H$, the inclusion of the spectrum) of the set over which bounds of the form $\|F(A)\|\le 2\sup_{z\in W(A)}\|F(z)\|$ for functions of $A$ are formulated.
--
--   **Formalization Note** The set is `numericalRange A` from the shared definitions and convexity is Mathlib's `Convex ℝ`, i.e. convexity over the real scalars. The standing completeness assumption on $H$ is explicitly omitted for this theorem.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HilbertCrouzeix/NumericalRange.lean#L182-L226

import Mathlib
import Definitions.Def_HilbertCrouzeix
import Definitions.Def_OAI_Analysis_HilbertCrouzeix_NumericalRange

open OAI OAI.HilbertCrouzeix
open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H]

theorem OAI.HilbertCrouzeix.convex_numericalRange (A : H →L[ℂ] H) : Convex ℝ (numericalRange A) := by sorry
