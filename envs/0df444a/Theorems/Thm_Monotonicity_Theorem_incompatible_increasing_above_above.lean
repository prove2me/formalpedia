-- Prove2me | Theorems.Thm_Monotonicity_Theorem_incompatible_increasing_above_above
-- name    : Monotonicity_Theorem.incompatible_increasing_above_above
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-11T15:59:01.452252+00:00
-- url     : https://prove2.me/theorems/5c4824fc-a930-4572-a778-4432c1ddc263
-- title:
--   Strict increase on a subwindow contradicts the above-above pattern
-- statement:
--   If f has the above-above sign pattern on a window, so every point is a strict local minimum with witnesses inside the window, and f is strictly increasing on a finite subwindow contained in it, then False. Local increase and everywhere-local-minima are incompatible.

import Definitions.Def_Monotonicity_Theorem_Framework

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.incompatible_increasing_above_above {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    {a b : Endpoint R} (hsubJ : forall x, openInterval D a b x -> I x)
    (hU : forall x (hxI : I x), openInterval D a b x ->
        exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
        Lt1 D c1 x /\ Lt1 D x c2 /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D c1 y -> Lt1 D y x ->
          Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D x y -> Lt1 D y c2 ->
          Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1))
    {u v : R} (huv : D.lt u v)
    (hsub : forall x, openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval D a b x)
    (hinc : forall x (hxI : I x) y (hyI : I y),
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y ->
      Lt1 D x y -> Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) :
    False := by sorry
