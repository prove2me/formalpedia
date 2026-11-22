-- Prove2me | Theorems.Thm_Monotonicity_Theorem_constant_or_injective_subinterval
-- name    : Monotonicity_Theorem.constant_or_injective_subinterval
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-13T06:03:24.699257+00:00
-- url     : https://prove2.me/theorems/8b74c668-6fae-47c8-a4a8-2e37d90fbaff
-- title:
--   A definable function is constant or injective on a subinterval
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and let $u < v$ be such that $(u,v) \subseteq I$.
--
--   **Claim.** There are $u_1 < v_1$ with $(u_1,v_1) \subseteq (u,v)$ such that $f$ is constant on $(u_1,v_1)$, or $f$ is injective on $(u_1,v_1)$:
--
--   $$\exists\, u_1 < v_1,\quad (u_1,v_1) \subseteq (u,v) \ \text{ and } \ \bigl(f\restriction(u_1,v_1) \text{ constant}\bigr) \ \text{ or } \ \bigl(f\restriction(u_1,v_1) \text{ injective}\bigr).$$
--
--   This is the first half of the local core of the Monotonicity Theorem. The argument is a dichotomy on the fibres of $f$ over $(u,v)$. Each fibre $f^{-1}(c) \cap (u,v)$ is a definable subset of the line, so by o-minimality it is either finite or contains an interval. If some fibre contains an interval $(u_1,v_1) \subseteq (u,v)$, then $f$ is constant there and the first alternative holds.
--
--   Otherwise every fibre meeting $(u,v)$ is finite. Then the image $f\bigl((u,v)\bigr)$ is a definable infinite subset of the line, hence contains an interval $J$. Sending each $c \in J$ to the least element of the finite nonempty set $f^{-1}(c) \cap (u,v)$ gives a definable injection $g : J \to (u,v)$ with $f \circ g = \mathrm{id}_J$, so $f$ is injective on the definable infinite set $g(J)$. By o-minimality $g(J)$ contains an interval $(u_1,v_1)$, which may moreover be shrunk to lie inside $(u,v)$, and $f$ is injective there.
--
--   **Formalization note.** Injectivity on $(u_1,v_1)$ is stated pointwise for points of $I$ lying in $(u_1,v_1)$: if two such points have equal $f$-values then they are equal. Constancy is the predicate `ConstOnInterval` of the mission's window-loci definitions.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1, proof of the Monotonicity Theorem (the two lemmas: on a subinterval a definable function is constant or injective; an injective definable function is strictly monotone on a further subinterval).

import Definitions.Def_Monotonicity_Theorem_Window_Loci

theorem Monotonicity_Theorem.constant_or_injective_subinterval {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I) :
    exists u1 v1 : R, D.lt u1 v1 /\
      (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) /\
      (ConstOnInterval f u1 v1 \/
        forall x (hx : I x), openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x ->
          forall y (hy : I y), openInterval D (Endpoint.finite u1) (Endpoint.finite v1) y ->
            f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y) := by sorry
