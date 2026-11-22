-- Prove2me | Theorems.Thm_Monotonicity_Theorem_finite_fiber_case_v4
-- name    : Monotonicity_Theorem.finite_fiber_case_v4
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T18:27:10.127462+00:00
-- url     : https://prove2.me/theorems/ee3ff6eb-8c48-4ea8-83d2-4121abb53c2c
-- title:
--   Finite fibers yield an injective subinterval
-- statement:
--   If every one-dimensional value fiber of a definable function is finite, then the function is injective on some subinterval of its infinite domain.
-- source:
--   monotonicity.tex, Lemma 1 finite-fiber inverse construction

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.finite_fiber_case_v4 {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (hI : IsInfinite1 I)
    (hfinite : ∀ z : Power R 1, IsFinite1 (fun x : Power R 1 =>
      I x ∧ ∃ hx : I x, (f.toFun ⟨x, hx⟩).1 = (fun _ : Fin 1 => z 0))) :
    ∃ a b : Endpoint R, Endpoint.lt D a b ∧
      (openInterval D a b).Subset I ∧
      (∀ x (hxI : I x), openInterval D a b x → ∀ y (hyI : I y), openInterval D a b y →
        f.toFun (Subtype.mk x hxI) = f.toFun (Subtype.mk y hyI) → x = y) := by sorry
