-- Prove2me | Theorems.Thm_Monotonicity_Theorem_infinite_image_of_finite_fibers
-- name    : Monotonicity_Theorem.infinite_image_of_finite_fibers
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T18:26:48.37574+00:00
-- url     : https://prove2.me/theorems/c5161d20-1dc2-4bed-a8f9-618d673059aa
-- title:
--   Finite fibers over an infinite domain give infinite image
-- statement:
--   If every value fiber of a definable function is finite but the domain is infinite, then the image is infinite. Otherwise a finite image listing combined with finite fiber listings would list the whole domain. This feeds the interval-extraction step of the Lemma 1 finite-fiber case.
-- source:
--   monotonicity.tex, Lemma 1 finite-fiber step; supporting infinitude lemma

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.infinite_image_of_finite_fibers {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (hI : IsInfinite1 I)
    (hfinite : forall z : Power R 1, IsFinite1 (fun x : Power R 1 =>
      I x /\ exists hx : I x, (f.toFun (Subtype.mk x hx)).1 = (fun _ : Fin 1 => z 0))) :
    IsInfinite1 (fun y : Power R 1 => exists x : Power R 1, exists hx : I x,
      (f.toFun (Subtype.mk x hx)).1 = y) := by sorry
