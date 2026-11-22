-- Prove2me | Theorems.Thm_Monotonicity_Theorem_good_outside_finite_exceptional_set
-- name    : Monotonicity_Theorem.good_outside_finite_exceptional_set
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T20:07:13.111062+00:00
-- url     : https://prove2.me/theorems/3ff58c68-ba0e-402f-8c52-8fe56e73d522
-- title:
--   Good outside a finite exceptional set
-- statement:
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and assume the domain $I$ is infinite.
--
--   **Claim.** There is a *finite* exceptional set $F \subseteq R$ such that every open interval $(u,v)$ with $u < v$ that contains no point of $F$ is **good** for $f$, where an open interval $J$ is called good when
--
--   $$\text{either } f \text{ is constant on } I \cap J, \qquad \text{or } f \text{ is strictly monotone on } I \cap J \text{ and } J \subseteq \mathrm{ContinuousPoints}(D, I, \mathrm{graph}\, f).$$
--
--   This is the o-minimal content of the finite-partition step of the Monotonicity Theorem: all the exceptional behaviour of a definable one-variable function (transition points between constancy, strict increase and strict decrease, isolated points and component endpoints of the domain, and points where no uniform behaviour holds on any window) is confined to finitely many points of the line. The exceptional set is obtained by applying o-minimality to the definable loci of points admitting a constant window, an increasing window, and a decreasing window respectively: each such locus is a finite union of points and intervals, and Lemmas 1--3 of the mission (constant-or-injective on a subinterval, injective implies locally strictly monotone, strictly monotone implies continuous on a subinterval) show that the set of points admitting no good window contains no interval, hence is finite.
--
--   Once this is available, the Monotonicity Theorem follows by choosing cut points that avoid $F$.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1 (Monotonicity Theorem); finite-exceptional-set step of the proof, corresponding to the assembly of Lemmas 1-3 of monotonicity.tex.

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.good_outside_finite_exceptional_set {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (hI : IsInfinite1 I) :
    exists F : Set (Power R 1), IsFinite1 F /\
      forall u v : R, D.lt u v ->
        (forall x : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) x -> Not (F x)) ->
        (let J : Set (Power R 1) := openInterval D (Endpoint.finite u) (Endpoint.finite v)
         ((forall x (hxI : I x), J x -> forall y (hyI : I y), J y ->
            f.toFun (Subtype.mk x hxI) = f.toFun (Subtype.mk y hyI)) \/
          (((forall x (hxI : I x), J x -> forall y (hyI : I y), J y -> Lt1 D x y ->
              Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) \/
            (forall x (hxI : I x), J x -> forall y (hyI : I y), J y -> Lt1 D x y ->
              Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)) /\
           J.Subset (ContinuousPoints D I
             (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun))))) := by sorry
