-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_linear_sum_limit
-- name    : Kyprianou.Ch04.kw48_linear_sum_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:54:14.062278+00:00
-- url     : https://prove2.me/theorems/7e450de1-4c92-43f0-a95f-4f42e62c8e57
-- title:
--   Linearised complex correction converges by both quadratures
-- statement:
--   Linearised complex correction converges by both quadratures.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The linearised complex correction is the prescribed linear
combination of the convergent record and time quadratures. -/

theorem Kyprianou.Ch04.kw48_linear_sum_limit {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (w : Ω) (a b : NNReal)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hTime : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((u n (i+1):Real)-(u n i:Real)) • Z L alpha beta (u n (i+1)) w)
      atTop (nhds (J L alpha beta b w-J L alpha beta a w)))
    (hRecord : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (runningSup L (u n (i+1)) w-runningSup L (u n i) w) •
        Z L alpha beta (u n (i+1)) w)
      atTop (nhds (S L beta b w-S L beta a w))) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      Z L alpha beta (u n (i+1)) w *
        (G L Psi alpha beta (u n (i+1)) w-G L Psi alpha beta (u n i) w))
      atTop (nhds (Complex.I*((beta-alpha:Real):Complex)*
        (S L beta b w-S L beta a w)-
        Psi alpha*(J L alpha beta b w-J L alpha beta a w))) := by sorry
