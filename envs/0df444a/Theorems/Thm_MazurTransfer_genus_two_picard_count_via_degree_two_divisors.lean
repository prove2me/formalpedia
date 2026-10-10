-- Prove2me | Theorems.Thm_MazurTransfer_genus_two_picard_count_via_degree_two_divisors
-- name    : MazurTransfer.genus_two_picard_count_via_degree_two_divisors
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T00:07:57.689994+00:00
-- url     : https://prove2.me/theorems/a0b48bb0-6162-4645-9ea2-639dc00c1ff8
-- title:
--   Finite-field genus-two Picard groups from effective degree-two divisor counts
-- statement:
--   Let $K$ be a finite field and $F/K$ a function field satisfying the one-dimensional curve and essential-finite-type conditions. Assume its full constant field is $K$, its actual genus is two, and its complete set $E_2(F/K)$ of effective degree-two divisors is finite. Then its genuine degree-zero divisor-class group is finite, and
--
--   $$|E_2(F/K)|=|\operatorname{Pic}^0_K(F)|+|K|.$$
--
--   The canonical degree-two class has $|K|+1$ effective representatives; every other degree-two class has exactly one. Riemann--Roch supplies an effective representative in every such class. No chosen rational place or Picard-cardinality assumption is required. Applied to the literal order-13 curves, the accepted full-constant-field/genus invariants and effective divisor counts 22 and 24 yield arithmetic Picard orders 19 over F3 and F5. Rational rank and reduction compatibility remain separate obligations.
-- source:
--   Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Separately checked generic canonical-class and finite-fibre-sum bridge by Vas and contributors; downstream MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Source attribution retained. All conclusions concern the genuine divisor-class quotient.

import Mathlib.FieldTheory.Perfect
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
open AlgebraicCurve

theorem MazurTransfer.genus_two_picard_count_via_degree_two_divisors.{u}
    (K F : Type u) [Field K] [Finite K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    [Finite {D : AlgebraicCurve.Divisor K F //
      (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2}]
    (hconst : AlgebraicCurve.ConstantsAreBase K F)
    (hgen : AlgebraicCurve.genusFF K F = 2) :
    Finite (AlgebraicCurve.Pic0 K F) ∧
      Nat.card {D : AlgebraicCurve.Divisor K F //
        (∀ v, 0 ≤ D v) ∧ AlgebraicCurve.Divisor.degree D = 2} =
        Nat.card (AlgebraicCurve.Pic0 K F) + Nat.card K := by sorry
