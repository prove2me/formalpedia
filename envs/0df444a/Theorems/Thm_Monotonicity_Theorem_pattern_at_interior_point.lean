-- Prove2me | Theorems.Thm_Monotonicity_Theorem_pattern_at_interior_point
-- name    : Monotonicity_Theorem.pattern_at_interior_point
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T18:25:48.015774+00:00
-- url     : https://prove2.me/theorems/5324cdce-4541-4caf-a28e-d64d7d8acbfc
-- title:
--   Every interior point has a local sign pattern
-- statement:
--   An interior point of the domain of an injective definable function on an interval satisfies one of the four local sign patterns: on some two-sided window in the domain, values stay strictly above or below on each side. This is the pointwise covering step of Lemma 2.
-- source:
--   monotonicity.tex, Lemma 2 covering step; pointwise pattern lemma

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.pattern_at_interior_point {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {a b : Endpoint R} {B : Set (Power R 1)}
    (f : DefinableFunction M (openInterval D a b) B)
    (hinj : forall x y (hx : openInterval D a b x) (hy : openInterval D a b y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y)
    {p : Power R 1} (hp : openInterval D a b p) :
    (exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
      Lt1 D c1 p /\ Lt1 D p c2 /\
      (forall y (hy : openInterval D a b y), Lt1 D c1 y -> Lt1 D y p ->
        Lt1 D (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1) /\
      (forall y (hy : openInterval D a b y), Lt1 D p y -> Lt1 D y c2 ->
        Lt1 D (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1)) \/
    (exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
      Lt1 D c1 p /\ Lt1 D p c2 /\
      (forall y (hy : openInterval D a b y), Lt1 D c1 y -> Lt1 D y p ->
        Lt1 D (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1) /\
      (forall y (hy : openInterval D a b y), Lt1 D p y -> Lt1 D y c2 ->
        Lt1 D (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1)) \/
    (exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
      Lt1 D c1 p /\ Lt1 D p c2 /\
      (forall y (hy : openInterval D a b y), Lt1 D c1 y -> Lt1 D y p ->
        Lt1 D (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1) /\
      (forall y (hy : openInterval D a b y), Lt1 D p y -> Lt1 D y c2 ->
        Lt1 D (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1)) \/
    (exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
      Lt1 D c1 p /\ Lt1 D p c2 /\
      (forall y (hy : openInterval D a b y), Lt1 D c1 y -> Lt1 D y p ->
        Lt1 D (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1) /\
      (forall y (hy : openInterval D a b y), Lt1 D p y -> Lt1 D y c2 ->
        Lt1 D (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1)) := by sorry
