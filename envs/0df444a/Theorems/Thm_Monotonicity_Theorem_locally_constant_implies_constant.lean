-- Prove2me | Theorems.Thm_Monotonicity_Theorem_locally_constant_implies_constant
-- name    : Monotonicity_Theorem.locally_constant_implies_constant
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T20:28:29.967575+00:00
-- url     : https://prove2.me/theorems/94515fe6-b5e7-4b51-b065-1adff06f69e3
-- title:
--   Locally constant implies constant
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints, let $f : I \to B$ be a definable function of one variable, and let $u < v$ be such that the open interval $(u,v)$ is contained in the domain $I$.
--
--   **Claim.** If every point of $(u,v)$ has an open neighbourhood on which $f$ is constant, then $f$ is constant on $(u,v)$:
--
--   $$(u,v) \subseteq I \ \text{ and } \ (u,v) \subseteq \{x : f \text{ is constant near } x\} \ \Longrightarrow\ f(x) = f(y) \ \text{ for all } x, y \in (u,v).$$
--
--   This is the passage from local to global constancy. Over a general dense linear order it is not a consequence of the local hypothesis alone, since there is no completeness available; it holds because the level set $\{z \in (u,v) : f(z) = f(x)\}$ is definable, and a nonempty definable subset of an interval which is open and relatively closed is the whole interval. The hypothesis $(u,v) \subseteq I$ cannot be dropped: for a domain consisting of isolated points, $f$ can be locally constant at every point and still take different values.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1 (Monotonicity Theorem); step of the proof of the finite-exceptional-set lemma of this mission.

import Definitions.Def_Monotonicity_Theorem_Window_Loci

theorem Monotonicity_Theorem.locally_constant_implies_constant {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hloc : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset (ConstWindowLocus f)) :
    ConstOnInterval f u v := by sorry
