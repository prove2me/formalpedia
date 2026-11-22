-- Prove2me | Theorems.Thm_Monotonicity_Theorem_left_adjacent_cut
-- name    : Monotonicity_Theorem.left_adjacent_cut
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T18:26:38.129015+00:00
-- url     : https://prove2.me/theorems/123bc9e2-9c72-46c3-9559-81152e4d0a3d
-- title:
--   Covered left windows have a pure adjacent cut above
-- statement:
--   If two definable sets cover a left window, some cut above the left endpoint yields a pure adjacent subwindow. Strengthens the adjacent-piece selection with the lower bound needed for domain membership of the cut.
-- source:
--   monotonicity.tex, Lemma 2 covering step; bounded selection lemma

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.left_adjacent_cut {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {A B : Set (Power R 1)}
    (hA : M.S 1 A) (hB : M.S 1 B)
    {c1 p : R} (hlt : D.lt c1 p)
    (hcov : forall x : Power R 1,
      openInterval D (Endpoint.finite c1) (Endpoint.finite p) x -> A x \/ B x) :
    exists c1' : R, D.lt c1' p /\ (D.lt c1 c1' \/ c1 = c1') /\
      ((forall x : Power R 1,
        openInterval D (Endpoint.finite c1') (Endpoint.finite p) x -> A x) \/
       (forall x : Power R 1,
        openInterval D (Endpoint.finite c1') (Endpoint.finite p) x -> B x)) := by sorry
