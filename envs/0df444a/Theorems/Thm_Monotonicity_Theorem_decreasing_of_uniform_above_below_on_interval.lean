-- Prove2me | Theorems.Thm_Monotonicity_Theorem_decreasing_of_uniform_above_below_on_interval
-- name    : Monotonicity_Theorem.decreasing_of_uniform_above_below_on_interval
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-13T06:35:30.89617+00:00
-- url     : https://prove2.me/theorems/b2ff1981-fe71-4a1d-976a-6a1b5188a6b5
-- title:
--   The above-below germ pattern forces strict decrease on the interval
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and let $u < v$ satisfy $(u,v) \subseteq I$.
--
--   **Claim.** If $f$ has the above-below germ pattern on $(u,v)$, then $f$ is strictly decreasing on $(u,v)$:
--
--   $$x < y \ \text{ in } (u,v) \ \Longrightarrow \ f(y) < f(x).$$
--
--   This is the mirror image of the increasing case. The hypothesis compares $f$ with the single value $f(x)$ immediately on each side of each point $x$, and the conclusion compares all pairs. The proof is the definable-connectedness argument applied to the definable set $\{z : f(z) < f(x)\}$ for a fixed $x$: it has finitely many boundary points, the right half of the germ pattern produces a point of it immediately to the right of any point already reached, and the left half shows it is inherited at a point from the points immediately to its left.
--
--   **Formalization note.** `UniformAboveBelow` is the predicate of the accompanying definitions and `DecOnInterval` the strict-decrease predicate of the mission's window-loci definitions.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1, proof of the Monotonicity Theorem (the step showing that an injective definable function is strictly monotone on a subinterval).

import Definitions.Def_Monotonicity_Theorem_Uniform_Germs

theorem Monotonicity_Theorem.decreasing_of_uniform_above_below_on_interval {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hU : UniformAboveBelow D f u v) :
    DecOnInterval f u v := by sorry
