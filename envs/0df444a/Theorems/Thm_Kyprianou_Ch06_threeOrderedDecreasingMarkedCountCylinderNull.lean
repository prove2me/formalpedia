-- Prove2me | Theorems.Thm_Kyprianou_Ch06_threeOrderedDecreasingMarkedCountCylinderNull
-- name    : Kyprianou.Ch06.threeOrderedDecreasingMarkedCountCylinderNull
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:23:07.147223+00:00
-- url     : https://prove2.me/theorems/42bceb44-10c2-45c2-8d43-eedc5736d367
-- title:
--   Three marked-Poisson cumulative observations at ordered times have zero probability if counts decrease
-- statement:
--   Under the source Chapter 6 marked Poisson almost-sure time-monotone sample-path count property, the triple count cylinder for a single mark set at ordered times s≤t≤u has probability zero whenever its prescribed levels decrease at either adjacent observation. Prove with a.e impossible-event reasoning and measure-null equivalence, preserving all original process assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.threeOrderedDecreasingMarkedCountCylinderNull
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B : Set E) (s t u : NNReal) (hst : s ≤ t) (htu : t ≤ u)
    (k l q : Nat) (hBad : l < k ∨ q < l) :
    P {omega | N omega s B = k ∧
      N omega t B = l ∧ N omega u B = q} = 0 := by sorry
