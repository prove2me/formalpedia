-- Prove2me | Theorems.Thm_Monotonicity_Theorem_minimals_infinite
-- name    : Monotonicity_Theorem.minimals_infinite
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T18:27:20.382984+00:00
-- url     : https://prove2.me/theorems/9103703d-f510-48c8-bde2-5e247fa8194b
-- title:
--   Fiber-minimal points are infinite
-- statement:
--   If every value fiber is finite but the domain is infinite, then the fiber-minimal points are infinite. Otherwise a finite minima listing would induce a finite image listing through minimum preimages, contradicting image infinitude. This supplies the infinite definable set for the final interval extraction of the Lemma 1 finite-fiber case.
-- source:
--   monotonicity.tex, Lemma 1 finite-fiber step; infinitude transfer lemma

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.minimals_infinite {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (hI : IsInfinite1 I)
    (hfinite : forall z : Power R 1, IsFinite1 (fun x : Power R 1 =>
      I x /\ exists hx : I x, (f.toFun (Subtype.mk x hx)).1 = (fun _ : Fin 1 => z 0))) :
    IsInfinite1 (fun x : Power R 1 => I x /\ ¬ exists w : Power R 1, I w /\ Lt1 D w x /\
      exists hxw : I w, exists hxx : I x,
        (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk x hxx)).1) := by sorry
