-- Prove2me | Theorems.Thm_OAI_MainGap_exists_norming_positive
-- name    : OAI.MainGap.exists_norming_positive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:01:59.159339+00:00
-- url     : https://prove2.me/theorems/476a2f86-2cb0-4e60-8cf9-e3b300a6f08c
-- title:
--   Every positive element is normed by a positive functional of norm at most one
-- statement:
--   Let $A$ be a unital C$^*$-algebra with $1\neq0$, ordered by its positive cone. A *positive linear functional* on a C$^*$-algebra $A$ is a $\mathbb{C}$-linear map $f:A\to\mathbb{C}$ that preserves order, where $\mathbb{C}$ carries the partial order $z\le w$ iff $\operatorname{Re}z\le\operatorname{Re}w$ and $\operatorname{Im}z=\operatorname{Im}w$. Equivalently, $f(a)$ is a nonnegative real number whenever $a\ge0$.
--
--   **Theorem.** For every positive element $d\in A$ there is a positive linear functional $f$ on $A$ such that
--   $$|f(a)|\le\|a\|\quad\text{for all }a\in A,\qquad\text{and}\qquad f(d)=\|d\| .$$
--
--   Combined with the GNS construction, such functionals produce Hilbert-space representations that detect prescribed elements. In this development the result is applied to elements of the form $d=x^*x$ in order to build a representation that annihilates a given closed ideal but not a given element outside it.
--
--   **Formalization Note** The order on $A$ is any partial order making $A$ a star-ordered ring, which in a C$^*$-algebra is necessarily the positive-cone order. The functional is a bundled positive linear map `A →ₚ[ℂ] ℂ`; the hypothesis `[Nontrivial A]` excludes the zero algebra, and the norm bound is stated pointwise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/PositiveFunctional.lean#L53-L89

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
variable {A : Type*} [CStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

theorem OAI.MainGap.exists_norming_positive [Nontrivial A] {d : A} (hd : 0 ≤ d) :
    ∃ f : A →ₚ[ℂ] ℂ, (∀ a, ‖f a‖ ≤ ‖a‖) ∧ f d = (‖d‖ : ℂ) := by sorry
