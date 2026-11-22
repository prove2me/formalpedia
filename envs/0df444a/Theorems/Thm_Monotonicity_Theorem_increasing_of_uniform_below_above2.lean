-- Prove2me | Theorems.Thm_Monotonicity_Theorem_increasing_of_uniform_below_above2
-- name    : Monotonicity_Theorem.increasing_of_uniform_below_above2
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-14T22:02:47.3272+00:00
-- url     : https://prove2.me/theorems/a56818c0-507a-4c53-b357-ac11190256b8
-- title:
--   Increasing on a uniform below-above window
-- statement:
--   If every point of a window has a below-above sign pattern, some subwindow has the function strictly increasing. The easy below-above case of Lemma 2. Retired: the window was not required to be nonempty, so the statement is false as stated; use Monotonicity_Theorem.increasing_of_uniform_below_above_corrected instead. Further retired 2026-09-14: old-framework statement superseded by the same-named new-framework formalization in the current staging proposal; the _corrected successor names are retired, use the clean names.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Definitions.Def_Monotonicity_Theorem_Framework2

theorem Monotonicity_Theorem.increasing_of_uniform_below_above2 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hinj : ∀ x y (hx : I x) (hy : I y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    {a b : Endpoint R} (hsubJ : ∀ x, openInterval a b x → I x)
    (hlt : Endpoint.lt a b)
    (hU : ∀ x (hxI : I x), openInterval a b x ->
        ∃ c1 c2 : Power R 1, openInterval a b c1 ∧ openInterval a b c2 ∧
        Lt1 c1 x ∧ Lt1 x c2 ∧
        (∀ y (hyI : I y), openInterval a b y → Lt1 c1 y → Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) ∧
        (∀ y (hyI : I y), openInterval a b y → Lt1 x y → Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)) :
    ∃ a2 b2 : Endpoint R, Endpoint.lt a2 b2 ∧
      (∀ x, openInterval a2 b2 x → I x) ∧
      (∀ x (hxI : I x) y (hyI : I y), openInterval a2 b2 x → openInterval a2 b2 y ->
        Lt1 x y → Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) := by sorry
