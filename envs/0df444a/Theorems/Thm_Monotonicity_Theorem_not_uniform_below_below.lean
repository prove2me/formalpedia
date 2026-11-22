-- Prove2me | Theorems.Thm_Monotonicity_Theorem_not_uniform_below_below
-- name    : Monotonicity_Theorem.not_uniform_below_below
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-13T06:53:14.377229+00:00
-- url     : https://prove2.me/theorems/587676e9-213a-4b3e-b10b-c407a461736c
-- title:
--   An injective definable function has no interval of strict local maxima
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and let $u<v$ satisfy $(u,v) \subseteq I$. Assume $f$ is injective on $(u,v)$.
--
--   **Claim.** $f$ cannot have the below-below germ pattern on $(u,v)$; that is, it is impossible that every point of $(u,v)$ is a strict local maximum of $f$.
--
--   This is the mirror image of the exclusion of the above-above pattern, and together with it completes the passage from the four-fold germ classification of an injective definable function to the dichotomy "strictly increasing or strictly decreasing on a subinterval". As in that case the hypothesis is consistent for arbitrary injective functions on a real interval, so the proof must use o-minimality.
--
--   A natural line of attack is through the running maxima. For an interval $K \subseteq (u,v)$ the sets
--
--   $$N(K) = \{\, x \in K : f(z) < f(x) \text{ for all } z \in K \text{ with } z < x \,\}, \qquad P(K) = \{\, x \in K : f(z) < f(x) \text{ for all } z \in K \text{ with } z > x \,\}$$
--
--   are definable, and $f$ is strictly increasing on $N(K)$ and strictly decreasing on $P(K)$. Under the hypothesis neither can contain an interval, since a point interior to an interval of strict monotonicity is not a strict local maximum; hence both are finite. Producing an infinite definable subset of $N(K)$ or of $P(K)$ therefore yields the contradiction.
--
--   **Formalization note.** `UniformBelowBelow` is the predicate of the accompanying definitions: every $x \in I \cap (u,v)$ has a window $c_1 < x < c_2$ inside $(u,v)$ with $f(y) < f(x)$ for every $y$ of the domain in $(c_1,x) \cup (x,c_2)$.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1, proof of the Monotonicity Theorem (the germ classification used in the step showing that an injective definable function is strictly monotone on a subinterval).

import Definitions.Def_Monotonicity_Theorem_Extremal_Germs

theorem Monotonicity_Theorem.not_uniform_below_below {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : forall x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      forall y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y ->
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y)
    (hU : UniformBelowBelow D f u v) :
    False := by sorry
