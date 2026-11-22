-- Prove2me | Theorems.Thm_Monotonicity_Theorem_locally_decreasing_implies_decreasing
-- name    : Monotonicity_Theorem.locally_decreasing_implies_decreasing
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T20:28:33.403535+00:00
-- url     : https://prove2.me/theorems/8996e598-11dc-4ed3-9b06-4c5936646820
-- title:
--   Locally strictly decreasing implies strictly decreasing
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints, let $f : I \to B$ be a definable function of one variable, and let $u < v$ be such that the open interval $(u,v)$ is contained in the domain $I$.
--
--   **Claim.** If every point of $(u,v)$ has an open neighbourhood, contained in $I$, on which $f$ is strictly decreasing, then $f$ is strictly decreasing on $(u,v)$:
--
--   $$x < y \ \text{ in } (u,v) \ \Longrightarrow\ f(y) < f(x).$$
--
--   This is the decreasing counterpart of the local-to-global statement for strict increase, and is proved in the same way; the two are exchanged by reversing the order on the codomain.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1 (Monotonicity Theorem); step of the proof of the finite-exceptional-set lemma of this mission.

import Definitions.Def_Monotonicity_Theorem_Window_Loci

theorem Monotonicity_Theorem.locally_decreasing_implies_decreasing {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hloc : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset (DecWindowLocus f)) :
    DecOnInterval f u v := by sorry
