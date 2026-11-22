-- Prove2me | Theorems.Thm_Monotonicity_Theorem_not_uniform_above_above
-- name    : Monotonicity_Theorem.not_uniform_above_above
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-13T06:53:12.732493+00:00
-- url     : https://prove2.me/theorems/be89cf2c-7985-4319-9ebb-05a5476b77fc
-- title:
--   An injective definable function has no interval of strict local minima
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and let $u<v$ satisfy $(u,v) \subseteq I$. Assume $f$ is injective on $(u,v)$.
--
--   **Claim.** $f$ cannot have the above-above germ pattern on $(u,v)$; that is, it is impossible that every point of $(u,v)$ is a strict local minimum of $f$.
--
--   This is one of the two exclusions that turn the four-fold germ classification of an injective definable function into the dichotomy "strictly increasing or strictly decreasing on a subinterval", and it is the substantive content of that step: for an arbitrary injective function on an interval of the real line the hypothesis is not absurd, so the proof must use o-minimality in an essential way.
--
--   A natural line of attack is through the running minima. For an interval $K \subseteq (u,v)$ the sets
--
--   $$N(K) = \{\, x \in K : f(z) > f(x) \text{ for all } z \in K \text{ with } z < x \,\}, \qquad P(K) = \{\, x \in K : f(z) > f(x) \text{ for all } z \in K \text{ with } z > x \,\}$$
--
--   are definable, and $f$ is strictly decreasing on $N(K)$ and strictly increasing on $P(K)$. Under the hypothesis neither can contain an interval, since a point interior to an interval of strict monotonicity is not a strict local minimum; hence both are finite. Producing an infinite definable subset of $N(K)$ or of $P(K)$ therefore yields the contradiction.
--
--   **Formalization note.** `UniformAboveAbove` is the predicate of the accompanying definitions: every $x \in I \cap (u,v)$ has a window $c_1 < x < c_2$ inside $(u,v)$ with $f(x) < f(y)$ for every $y$ of the domain in $(c_1,x) \cup (x,c_2)$.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1, proof of the Monotonicity Theorem (the germ classification used in the step showing that an injective definable function is strictly monotone on a subinterval).

import Definitions.Def_Monotonicity_Theorem_Extremal_Germs

theorem Monotonicity_Theorem.not_uniform_above_above {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : forall x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      forall y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y ->
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y)
    (hU : UniformAboveAbove D f u v) :
    False := by sorry
