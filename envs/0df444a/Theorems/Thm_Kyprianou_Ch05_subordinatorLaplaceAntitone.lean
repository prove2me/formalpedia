-- Prove2me | Theorems.Thm_Kyprianou_Ch05_subordinatorLaplaceAntitone
-- name    : Kyprianou.Ch05.subordinatorLaplaceAntitone
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T17:25:39.857526+00:00
-- url     : https://prove2.me/theorems/f5acc300-cefd-5ad3-9891-a363d109a2f6
-- title:
--   Monotone sample paths imply antitonicity of the Laplace transform.
-- statement:
--   Monotone sample paths imply antitonicity of the Laplace transform.
-- source:
--   Kyprianou (2006), Lemma 5.2; faithful further decomposition of the time-Laplace semigroup and monotone additive linearity.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.subordinatorLaplaceAntitone
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (theta : Real) (htheta : 0 < theta) :
    Antitone (fun t : NNReal => (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P)) := by sorry
