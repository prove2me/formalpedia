-- Prove2me | Theorems.Thm_Monotonicity_Theorem_injective_implies_monotone_subinterval
-- name    : Monotonicity_Theorem.injective_implies_monotone_subinterval
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-13T06:03:26.268145+00:00
-- url     : https://prove2.me/theorems/c11871e9-fa0b-4c7b-8054-1165987e1740
-- title:
--   An injective definable function is strictly monotone on a subinterval
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and let $u < v$ satisfy $(u,v) \subseteq I$. Assume $f$ is injective on $(u,v)$, that is
--
--   $$x, y \in (u,v),\quad f(x) = f(y) \ \Longrightarrow\ x = y.$$
--
--   **Claim.** There are $u_1 < v_1$ with $(u_1,v_1) \subseteq (u,v)$ on which $f$ is strictly increasing or strictly decreasing.
--
--   This is the second half of the local core of the Monotonicity Theorem. The proof is again an application of o-minimality to a family of definable subsets of the line. Fix $x \in (u,v)$. By injectivity the two definable sets
--
--   $$A_x = \{\, y \in (x,v) : f(y) > f(x) \,\},\qquad B_x = \{\, y \in (x,v) : f(y) < f(x) \,\}$$
--
--   partition $(x,v)$. By o-minimality each of them is a finite union of points and intervals, so exactly one of them contains an interval with left endpoint $x$; thus $f$ is, immediately to the right of every point, either above or below its value at that point. The set of $x$ for which the first behaviour occurs is definable, hence it or its complement contains an interval, and on such an interval the local behaviour is uniform. A uniform one-sided comparison on an interval propagates to strict monotonicity on that interval, giving the required $(u_1,v_1)$.
--
--   **Formalization note.** `IncOnInterval` and `DecOnInterval` are the predicates of the mission's window-loci definitions, stated for the points of $I$ lying in the interval. The hypothesis $(u,v) \subseteq I$ records that the interval lies in the domain of $f$.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1, proof of the Monotonicity Theorem (the two lemmas: on a subinterval a definable function is constant or injective; an injective definable function is strictly monotone on a further subinterval).

import Definitions.Def_Monotonicity_Theorem_Window_Loci

theorem Monotonicity_Theorem.injective_implies_monotone_subinterval {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : forall x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      forall y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y ->
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y) :
    exists u1 v1 : R, D.lt u1 v1 /\
      (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) /\
      (IncOnInterval f u1 v1 \/ DecOnInterval f u1 v1) := by sorry
