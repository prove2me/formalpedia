-- Prove2me | Theorems.Thm_Monotonicity_Theorem_exists_germ_class_subinterval
-- name    : Monotonicity_Theorem.exists_germ_class_subinterval
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-13T06:53:04.71279+00:00
-- url     : https://prove2.me/theorems/c64ec535-2609-41ad-923f-16069358102e
-- title:
--   On a subinterval the germ class of an injective definable function is constant
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and let $u<v$ satisfy $(u,v) \subseteq I$. Assume $f$ is injective on $(u,v)$.
--
--   **Claim.** There are $u_1 < v_1$ with $(u_1,v_1) \subseteq (u,v)$ on which one of the four germ patterns of $f$ holds uniformly: below-above, above-below, above-above, or below-below.
--
--   This is the classification step in the analysis of an injective definable function of one variable. It is a pure consequence of o-minimality, and it does not yet decide which of the four classes occurs.
--
--   The argument has three parts. First, the germ dichotomy: a definable subset $A$ of the line either contains or misses an interval with endpoint $x$, on each side of $x$, because $A$ is a finite union of points and intervals. Second, for each $x$ the two definable sets
--   $$\{\, y : f(y) > f(x) \,\}, \qquad \{\, y : f(y) < f(x) \,\}$$
--   cover the punctured neighbourhoods of $x$ inside $(u,v)$, by injectivity; so the germ dichotomy assigns to each side of $x$ one of the two comparisons, and $x$ falls into exactly one of the four classes. Third, the four classes are definable subsets of the line, since each is defined by a first-order condition on $x$ built from the graph of $f$ and the order; their union is the infinite set $(u,v)$, so one of them is infinite and therefore contains an interval, which may be shrunk to lie inside $(u,v)$.
--
--   **Formalization note.** The four patterns are the predicates `UniformBelowAbove`, `UniformAboveBelow`, `UniformAboveAbove` and `UniformBelowBelow` of the accompanying definitions; each requires the witnessing window to lie inside the interval on which the pattern is asserted.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1, proof of the Monotonicity Theorem (the germ classification used in the step showing that an injective definable function is strictly monotone on a subinterval).

import Definitions.Def_Monotonicity_Theorem_Extremal_Germs

theorem Monotonicity_Theorem.exists_germ_class_subinterval {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : forall x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      forall y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y ->
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y) :
    exists u1 v1 : R, D.lt u1 v1 /\
      (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) /\
      (UniformBelowAbove D f u1 v1 \/ UniformAboveBelow D f u1 v1 \/
        UniformAboveAbove D f u1 v1 \/ UniformBelowBelow D f u1 v1) := by sorry
