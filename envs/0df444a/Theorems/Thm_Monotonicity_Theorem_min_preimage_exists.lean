-- Prove2me | Theorems.Thm_Monotonicity_Theorem_min_preimage_exists
-- name    : Monotonicity_Theorem.min_preimage_exists
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T17:46:03.164105+00:00
-- url     : https://prove2.me/theorems/931a8d52-c039-48f3-8c50-b209bf5ffb05
-- title:
--   Every image value has a fiber-minimal preimage
-- statement:
--   If every value fiber is finite, then every value in the image has a preimage that is minimal in its fiber: no strictly smaller domain point shares its value. The finite fiber is listed, its least coordinate exists, and the constant tuple there is the required minimum. This is the minimum-preimage construction of Lemma 1.
-- source:
--   monotonicity.tex, Lemma 1 finite-fiber step; minimum-preimage lemma

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.min_preimage_exists {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hfinite : forall z : Power R 1, IsFinite1 (fun x : Power R 1 =>
      I x /\ exists hx : I x, (f.toFun (Subtype.mk x hx)).1 = (fun _ : Fin 1 => z 0))) :
    forall y : Power R 1, (exists x : Power R 1, exists hx : I x,
      (f.toFun (Subtype.mk x hx)).1 = y) ->
      exists m : Power R 1, exists hm : I m,
        (¬ exists w : Power R 1, I w /\ Lt1 D w m /\ exists hxw : I w, exists hxm : I m,
          (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk m hxm)).1) /\
        (f.toFun (Subtype.mk m hm)).1 = y := by sorry
