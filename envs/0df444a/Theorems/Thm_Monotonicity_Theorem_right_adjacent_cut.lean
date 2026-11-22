-- Prove2me | Theorems.Thm_Monotonicity_Theorem_right_adjacent_cut
-- name    : Monotonicity_Theorem.right_adjacent_cut
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T18:24:59.086549+00:00
-- url     : https://prove2.me/theorems/7df2b99b-44ec-42f0-bf1c-9320606f61f5
-- title:
--   Covered right windows have a pure adjacent cut below
-- statement:
--   If two definable sets cover a right window, some cut below the right endpoint yields a pure adjacent subwindow. Mirror of the bounded left-sided selection step of Lemma 2.
-- source:
--   monotonicity.tex, Lemma 2 covering step; bounded selection lemma

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.right_adjacent_cut {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {A B : Set (Power R 1)}
    (hA : M.S 1 A) (hB : M.S 1 B)
    {p c2 : R} (hlt : D.lt p c2)
    (hcov : forall x : Power R 1,
      openInterval D (Endpoint.finite p) (Endpoint.finite c2) x -> A x \/ B x) :
    exists m : R, D.lt p m /\ (D.lt m c2 \/ m = c2) /\
      ((forall x : Power R 1,
        openInterval D (Endpoint.finite p) (Endpoint.finite m) x -> A x) \/
       (forall x : Power R 1,
        openInterval D (Endpoint.finite p) (Endpoint.finite m) x -> B x)) := by sorry
