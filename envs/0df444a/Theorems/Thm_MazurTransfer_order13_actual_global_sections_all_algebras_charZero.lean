-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_global_sections_all_algebras_charZero
-- name    : MazurTransfer.order13_actual_global_sections_all_algebras_charZero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T09:22:02.7027+00:00
-- url     : https://prove2.me/theorems/d737bde8-f537-42df-a8d8-836fd74a15b1
-- title:
--   Global sections after every algebra base change of the actual order-13 curve
-- statement:
--   Let K be any characteristic-zero field and let C/K be the actual unchanged order-13 curve y²=x⁶+2x⁵+x⁴+2x³+6x²+4x+1, constructed by gluing its ordinary and reciprocal charts. For every commutative K-algebra A, the canonical map A → Γ(C ×_K Spec A, O) is bijective. In particular this applies to K=ℚ and every commutative ℚ-algebra. The proof derives the rank-one field-fibre cohomology input from the actual curve and flat kernel base change. It does not assume algebraic closedness, geometric integrality or Picard representability, and it does not claim the Mazur torsion classification.
-- source:
--   Actual curve and cohomology: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . Flat kernel base change and global-section spreading: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Apache-2.0; original attribution retained. Unconditional actual-curve specialization by Vas and contributors.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem MazurTransfer.order13_actual_global_sections_all_algebras_charZero.{u} (K : Type u) [Field K] [CharZero K]
    (A : Type u) [CommRing A] [Algebra K A] :
    let c := MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap K A)) ⊤
    Function.Bijective (algebraMap A
      Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap K A), ⊤)) := by sorry
