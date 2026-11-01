-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_convex_closure_dom
-- name    : InconsistentDR.Shadow.convex_closure_dom
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T23:49:45.666206+00:00
-- url     : https://prove2.me/theorems/95c2a4dd-ee56-4b0c-88d9-9192c118bbd6
-- title:
--   $\overline{\operatorname{dom}}\,A$ is convex for a monotone $A$ with full-domain resolvent ([6, Cor. 21.14], used in (4b))
-- statement:
--   Let $X$ be a real Hilbert space and let $A:X\rightrightarrows X$ be a monotone operator whose resolvent $J_A=(\mathrm{Id}+A)^{-1}$ is defined everywhere; that is, there is a map $J:X\to X$ with
--   $$x-J(x)\in A\big(J(x)\big)\qquad\text{for every }x\in X.$$
--   (By Minty's theorem this holds exactly when $A$ is maximally monotone.) Then the closure of the domain of $A$ is convex:
--   $$\overline{\operatorname{dom}}\,A\ \text{ is a convex set.}$$
--
--   This is Bauschke–Combettes, Corollary 21.14 (a consequence of Minty's theorem). It is used throughout the paper whenever $v_D=P_{\overline D}(0)$ and $v_R=P_{\overline R}(0)$ are treated as projections onto closed convex sets, for instance in (4b), (35), (40), Proposition 4.2 and Theorem 4.3. Applied to $A^{-1}$, whose resolvent is $\mathrm{Id}-J_A$, it also gives convexity of $\overline{\operatorname{ran}}\,A$.
--
--   **Formalization Note** Monotonicity is the published `IsMonotoneOp`, $\operatorname{dom}A=\{x: Ax\neq\varnothing\}$ is the published `dom`, and the resolvent is supplied as a map `J` with `IsResolvent 1 A J`. `CompleteSpace X` makes $X$ a Hilbert space.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (2021), p. 2, (4b), and proof of Lemma 3.2, p. 9 (citing [6, Corollary 21.14]); Bauschke–Combettes, Convex Analysis and Monotone Operator Theory in Hilbert Spaces, Corollary 21.14

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators

namespace InconsistentDR.Shadow

open ThreeOpSplitting.Convergence

/-- [6, Corollary 21.14], used for (4b), p. 2: if `A` is monotone with a resolvent
`J = (Id + A)⁻¹` defined on all of `X` (so `A` is maximally monotone), then `cl dom A` is convex. -/
theorem convex_closure_dom {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X)
    (hJ : IsResolvent 1 A J) :
    Convex ℝ (closure (dom A)) := by sorry

end InconsistentDR.Shadow
