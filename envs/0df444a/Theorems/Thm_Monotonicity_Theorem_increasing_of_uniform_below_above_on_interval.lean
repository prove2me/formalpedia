-- Prove2me | Theorems.Thm_Monotonicity_Theorem_increasing_of_uniform_below_above_on_interval
-- name    : Monotonicity_Theorem.increasing_of_uniform_below_above_on_interval
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-13T06:35:31.99925+00:00
-- url     : https://prove2.me/theorems/8474b1f3-c7d4-45fb-92f4-cc34f672d6b6
-- title:
--   The below-above germ pattern forces strict increase on the interval
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and let $u < v$ satisfy $(u,v) \subseteq I$.
--
--   **Claim.** If $f$ has the below-above germ pattern on $(u,v)$, then $f$ is strictly increasing on $(u,v)$:
--
--   $$x < y \ \text{ in } (u,v) \ \Longrightarrow \ f(x) < f(y).$$
--
--   The hypothesis only compares $f$ with the single value $f(x)$ immediately to the left and to the right of each point $x$; the conclusion is a genuinely global statement about all pairs of points of the interval. The passage from one to the other is the standard definable-connectedness argument: for fixed $x$ the set $\{z : f(z) > f(x)\}$ is definable, so it has finitely many boundary points, and the right half of the germ pattern produces a point of this set immediately to the right of any point already reached, while the left half shows that the set is inherited at a point from the points immediately to its left. Hence the set contains every point of $(u,v)$ above $x$.
--
--   **Formalization note.** `UniformBelowAbove` is the predicate of the accompanying definitions and `IncOnInterval` the strict-increase predicate of the mission's window-loci definitions.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1, proof of the Monotonicity Theorem (the step showing that an injective definable function is strictly monotone on a subinterval).

import Definitions.Def_Monotonicity_Theorem_Uniform_Germs

theorem Monotonicity_Theorem.increasing_of_uniform_below_above_on_interval {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hU : UniformBelowAbove D f u v) :
    IncOnInterval f u v := by sorry
