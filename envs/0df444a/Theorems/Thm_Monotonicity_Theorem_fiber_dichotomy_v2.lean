-- Prove2me | Theorems.Thm_Monotonicity_Theorem_fiber_dichotomy_v2
-- name    : Monotonicity_Theorem.fiber_dichotomy_v2
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T17:45:53.467205+00:00
-- url     : https://prove2.me/theorems/9294ba1a-fb76-4f78-9ee9-de86d66b5c14
-- title:
--   Definable fibers split into an infinite or finite case
-- statement:
--   For a definable function, either some definable value fiber is infinite, or every value fiber is finite.
-- source:
--   monotonicity.tex, Lemma 1 case split

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.fiber_dichotomy_v2 {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    (∃ z : Power R 1,
      (M.S 1 (fun x : Power R 1 => I x ∧ ∃ hx : I x,
        (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0)) ∧
       IsInfinite1 (fun x : Power R 1 => I x ∧ ∃ hx : I x,
        (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0)))) ∨
    ∀ z : Power R 1, IsFinite1 (fun x : Power R 1 => I x ∧ ∃ hx : I x,
      (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0)) := by sorry
