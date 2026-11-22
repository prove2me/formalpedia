-- Prove2me | Theorems.Thm_Monotonicity_Theorem_exists_monotone_subinterval
-- name    : Monotonicity_Theorem.exists_monotone_subinterval
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T21:10:19.808554+00:00
-- url     : https://prove2.me/theorems/ea950b25-545e-4a67-9810-5e627f95320b
-- title:
--   A definable function is constant or strictly monotone on a subinterval
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and let $u < v$ be such that the open interval $(u,v)$ is contained in the domain $I$.
--
--   **Claim.** There are $u_1 < v_1$ with $(u_1,v_1) \subseteq (u,v)$ such that $f$ is constant on $(u_1,v_1)$, or strictly increasing on $(u_1,v_1)$, or strictly decreasing on $(u_1,v_1)$:
--
--   $$\exists\, u_1 < v_1,\quad (u_1,v_1) \subseteq (u,v) \ \text{ and } \ f\restriction(u_1,v_1) \ \text{is constant, strictly increasing, or strictly decreasing.}$$
--
--   This is the local core of the Monotonicity Theorem. The usual argument has two halves. First, either some fibre $f^{-1}(c)$ has nonempty interior inside $(u,v)$ — and then $f$ is constant on a subinterval — or every fibre is finite; in the latter case the image of $(u,v)$ is infinite, hence contains an interval, and taking the least preimage of each value yields a definable injection, so $f$ is injective on a subinterval. Second, an injective definable function on an interval is strictly monotone on some subinterval: for each $x$ the definable sets $\{y > x : f(y) > f(x)\}$ and $\{y > x : f(y) < f(x)\}$ partition a one-sided neighbourhood, so by o-minimality $f$ is locally strictly increasing or locally strictly decreasing to the right of every point, and one of the two behaviours persists on a whole subinterval.
--
--   Note that no hypothesis of infinitude of $I$ is needed beyond $(u,v) \subseteq I$, which already forces $I$ to be infinite, and that the conclusion is exactly what is required to produce a good window around every point of $(u_1,v_1)$.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1, proof of the Monotonicity Theorem (Lemmas 1-3: on a subinterval a definable function is constant or injective, and an injective definable function is strictly monotone on a further subinterval).

import Definitions.Def_Monotonicity_Theorem_Window_Loci

theorem Monotonicity_Theorem.exists_monotone_subinterval {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I) :
    exists u1 v1 : R, D.lt u1 v1 /\
      (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) /\
      (ConstOnInterval f u1 v1 \/ IncOnInterval f u1 v1 \/ DecOnInterval f u1 v1) := by sorry
