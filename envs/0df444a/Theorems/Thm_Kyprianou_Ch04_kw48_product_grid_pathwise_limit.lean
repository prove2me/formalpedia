-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_product_grid_pathwise_limit
-- name    : Kyprianou.Ch04.kw48_product_grid_pathwise_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:46:05.158949+00:00
-- url     : https://prove2.me/theorems/a97f7896-14e6-4e0b-824f-3d32b362ffd5
-- title:
--   Complex product-grid transfer to the actual signed process increment
-- statement:
--   Complex product-grid transfer to the actual signed process increment.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_product
import Theorems.Thm_Kyprianou_Ch04_kw48_discrete_product_summation
import Theorems.Thm_Kyprianou_Ch04_kw48_product_grid_transfer
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The correction limit implies the signed actual process increment limit. -/

theorem Kyprianou.Ch04.kw48_product_grid_pathwise_limit {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (a b : NNReal) (w : Ω)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (hCorr : Tendsto (fun n => C L Psi alpha beta (u n) (N n) w)
      atTop (nhds (Complex.I*((beta-alpha:Real):Complex)*
        (S L beta b w-S L beta a w) -
        Psi alpha*(J L alpha beta b w-J L alpha beta a w)))) :
    Tendsto (fun n => Q L Psi alpha beta (u n) (N n) w)
      atTop (nhds (M L Psi alpha beta a w-M L Psi alpha beta b w)) := by sorry
