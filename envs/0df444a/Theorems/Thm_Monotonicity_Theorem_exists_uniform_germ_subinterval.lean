-- Prove2me | Theorems.Thm_Monotonicity_Theorem_exists_uniform_germ_subinterval
-- name    : Monotonicity_Theorem.exists_uniform_germ_subinterval
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-13T06:35:27.211795+00:00
-- url     : https://prove2.me/theorems/f4571214-c831-4fc6-8eca-a8e14ed536ed
-- title:
--   An injective definable function has a uniform germ pattern on a subinterval
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and let $u < v$ satisfy $(u,v) \subseteq I$. Assume $f$ is injective on $(u,v)$.
--
--   **Claim.** There are $u_1 < v_1$ with $(u_1,v_1) \subseteq (u,v)$ such that, on $(u_1,v_1)$, $f$ has the below-above germ pattern, or $f$ has the above-below germ pattern:
--
--   $$\exists\, u_1 < v_1,\quad (u_1,v_1) \subseteq (u,v) \ \text{ and } \ \bigl(\mathrm{UniformBelowAbove}(u_1,v_1)\ \text{ or }\ \mathrm{UniformAboveBelow}(u_1,v_1)\bigr).$$
--
--   This is the germ-theoretic heart of the step "an injective definable function is strictly monotone on a subinterval". The two patterns are defined in the accompanying definitions: below-above says that every point $x$ of the interval has a window $c_1 < x < c_2$ inside the interval with $f < f(x)$ on $(c_1,x)$ and $f > f(x)$ on $(x,c_2)$; above-below is the mirror image.
--
--   Two ingredients are involved. The first is elementary o-minimality: for a definable subset $A$ of the line and a point $x$, $A$ either contains or misses an interval with endpoint $x$ on each side, because $A$ is a finite union of points and intervals. Applying this to the definable sets $\{y : f(y) > f(x)\}$ and $\{y : f(y) < f(x)\}$, whose union covers a punctured neighbourhood of $x$ by injectivity, shows that each point of $(u,v)$ falls into exactly one of four germ classes: below-above, above-below, below-below and above-above. The four classes are definable subsets of the line, so one of them contains a subinterval.
--
--   The second ingredient is the exclusion of the two extremal classes. On an interval of the above-above class every point would be a strict local minimum of $f$, and on an interval of the below-below class every point would be a strict local maximum; neither is possible for a definable injective function, and ruling them out is the substantive part of the claim.
--
--   **Formalization note.** Injectivity on $(u,v)$ is stated pointwise for points of $I$ lying in $(u,v)$. The two patterns are the predicates `UniformBelowAbove` and `UniformAboveBelow` of the accompanying definitions.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1, proof of the Monotonicity Theorem (the step showing that an injective definable function is strictly monotone on a subinterval).

import Definitions.Def_Monotonicity_Theorem_Uniform_Germs

theorem Monotonicity_Theorem.exists_uniform_germ_subinterval {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : forall x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      forall y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y ->
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y) :
    exists u1 v1 : R, D.lt u1 v1 /\
      (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) /\
      (UniformBelowAbove D f u1 v1 \/ UniformAboveBelow D f u1 v1) := by sorry
