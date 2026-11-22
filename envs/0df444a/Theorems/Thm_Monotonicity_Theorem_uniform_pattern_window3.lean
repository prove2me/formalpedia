-- Prove2me | Theorems.Thm_Monotonicity_Theorem_uniform_pattern_window3
-- name    : Monotonicity_Theorem.uniform_pattern_window3
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-15T00:21:11.525099+00:00
-- url     : https://prove2.me/theorems/bd9b97b7-ad21-43d4-bfc8-48c1a0ac253d
-- title:
--   Uniform pattern window
-- statement:
--   An injective definable map has a subwindow on which one of four sign patterns holds uniformly: above-above, above-below, below-above, or below-below. The uniform pattern feeds the four monotone-window lemmas.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Definitions.Def_Monotonicity_Theorem_Framework2

theorem Monotonicity_Theorem.uniform_pattern_window3 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hinj : forall (x : Power R 1), forall (y : Power R 1), forall (hx : I x), forall (hy : I y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y)
    {a0 b0 : Endpoint R} (hsub0 : (openInterval a0 b0).Subset I)
    (hlt0 : Endpoint.lt a0 b0) :
    exists (a : Endpoint R), exists (b : Endpoint R), Endpoint.lt a b /\
      (forall x, openInterval a b x -> openInterval a0 b0 x) /\
      ((forall (x : Power R 1), forall (hxI : I x), openInterval a b x ->
        exists (c1 : Power R 1), exists (c2 : Power R 1), openInterval a b c1 /\ openInterval a b c2 /\
        Lt1 c1 x /\ Lt1 x c2 /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 c1 y -> Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 x y -> Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)) \/
      (forall (x : Power R 1), forall (hxI : I x), openInterval a b x ->
        exists (c1 : Power R 1), exists (c2 : Power R 1), openInterval a b c1 /\ openInterval a b c2 /\
        Lt1 c1 x /\ Lt1 x c2 /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 c1 y -> Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 x y -> Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)) \/
      (forall (x : Power R 1), forall (hxI : I x), openInterval a b x ->
        exists (c1 : Power R 1), exists (c2 : Power R 1), openInterval a b c1 /\ openInterval a b c2 /\
        Lt1 c1 x /\ Lt1 x c2 /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 c1 y -> Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 x y -> Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)) \/
      (forall (x : Power R 1), forall (hxI : I x), openInterval a b x ->
        exists (c1 : Power R 1), exists (c2 : Power R 1), openInterval a b c1 /\ openInterval a b c2 /\
        Lt1 c1 x /\ Lt1 x c2 /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 c1 y -> Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 x y -> Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1))) := by sorry
