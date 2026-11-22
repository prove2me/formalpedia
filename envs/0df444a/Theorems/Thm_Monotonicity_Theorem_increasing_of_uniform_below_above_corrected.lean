-- Prove2me | Theorems.Thm_Monotonicity_Theorem_increasing_of_uniform_below_above_corrected
-- name    : Monotonicity_Theorem.increasing_of_uniform_below_above_corrected
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-11T13:36:27.835659+00:00
-- url     : https://prove2.me/theorems/7d0a02d2-1168-4986-8ea6-c27ff0e77603
-- title:
--   Uniform below-above pattern gives increase
-- statement:
--   If every point of a nonempty window has a below-above sign pattern, some subwindow has the function strictly increasing.

import Definitions.Def_Monotonicity_Theorem_Framework

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.increasing_of_uniform_below_above_corrected {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hinj : forall x y (hx : I x) (hy : I y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y)
    {a b : Endpoint R} (hsubJ : forall x, openInterval D a b x -> I x)
    (hlt : Endpoint.lt D a b)
    (hU : forall x (hxI : I x), openInterval D a b x ->
        exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
        Lt1 D c1 x /\ Lt1 D x c2 /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D c1 y -> Lt1 D y x ->
          Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D x y -> Lt1 D y c2 ->
          Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)) :
    exists a2 b2 : Endpoint R, Endpoint.lt D a2 b2 /\
      (forall x, openInterval D a2 b2 x -> I x) /\
      (forall x (hxI : I x) y (hyI : I y), openInterval D a2 b2 x -> openInterval D a2 b2 y ->
        Lt1 D x y -> Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) := by sorry
