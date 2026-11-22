-- Prove2me | Theorems.Thm_Monotonicity_Theorem_locally_increasing_implies_increasing
-- name    : Monotonicity_Theorem.locally_increasing_implies_increasing
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T20:28:34.642571+00:00
-- url     : https://prove2.me/theorems/6686f43c-de49-4fa4-b839-bf8004fbbea1
-- title:
--   Locally strictly increasing implies strictly increasing
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints, let $f : I \to B$ be a definable function of one variable, and let $u < v$ be such that the open interval $(u,v)$ is contained in the domain $I$.
--
--   **Claim.** If every point of $(u,v)$ has an open neighbourhood, contained in $I$, on which $f$ is strictly increasing, then $f$ is strictly increasing on $(u,v)$:
--
--   $$x < y \ \text{ in } (u,v) \ \Longrightarrow\ f(x) < f(y).$$
--
--   This is the passage from local to global strict increase. As in the constancy case it rests on definability: the set of points $z$ of $(u,v)$ for which $f$ is strictly increasing on the part of $(u,v)$ below $z$ is definable, open and relatively closed, hence all of $(u,v)$.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1 (Monotonicity Theorem); step of the proof of the finite-exceptional-set lemma of this mission.

import Definitions.Def_Monotonicity_Theorem_Window_Loci

theorem Monotonicity_Theorem.locally_increasing_implies_increasing {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hloc : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset (IncWindowLocus f)) :
    IncOnInterval f u v := by sorry
