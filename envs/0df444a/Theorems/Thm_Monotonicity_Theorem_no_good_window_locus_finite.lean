-- Prove2me | Theorems.Thm_Monotonicity_Theorem_no_good_window_locus_finite
-- name    : Monotonicity_Theorem.no_good_window_locus_finite
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T20:28:26.281401+00:00
-- url     : https://prove2.me/theorems/b3e99336-6592-4d4c-91b1-d2833841d818
-- title:
--   Only finitely many points admit no good window
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, and let $f : I \to B$ be a definable function of one variable with $I$ infinite. Call a point $x$ of the line *good* if some open interval $(u,v)$ containing $x$ witnesses one of
--
--   1. $f$ is constant on $I \cap (u,v)$;
--   2. $(u,v) \subseteq I$ and $f$ is strictly increasing on $(u,v)$;
--   3. $(u,v) \subseteq I$ and $f$ is strictly decreasing on $(u,v)$.
--
--   **Claim.** The set of points that are not good is finite.
--
--   The set of non-good points is definable, so by o-minimality it is a finite union of points and intervals; it therefore suffices to know that it contains no open interval. That in turn is the content of Lemmas 1–3 of this mission: on a subinterval, a definable function is constant or injective, an injective definable function is strictly monotone on a further subinterval, and the monotone situation can be arranged inside the domain. Consequently every open interval contains a point admitting a good window, so the non-good set has empty interior and is finite. Geometrically it consists of the finitely many transition points between the three regimes together with the finitely many boundary and isolated points of the domain.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1 (Monotonicity Theorem); step of the proof of the finite-exceptional-set lemma of this mission.

import Definitions.Def_Monotonicity_Theorem_Window_Loci

theorem Monotonicity_Theorem.no_good_window_locus_finite {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (hI : IsInfinite1 I) :
    IsFinite1 (setCompl (GoodWindowLocus f)) := by sorry
