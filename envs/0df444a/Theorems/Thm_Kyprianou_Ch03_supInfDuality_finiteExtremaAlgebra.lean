-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfDuality_finiteExtremaAlgebra
-- name    : Kyprianou.Ch03.supInfDuality_finiteExtremaAlgebra
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:02:17.07088+00:00
-- url     : https://prove2.me/theorems/0157f637-85ca-4b54-bee0-ad13ba2eaae4
-- title:
--   Translation and negation of finite extrema
-- statement:
--   Translation shifts the maximum of a finite nonempty real family, and negation exchanges maximum and negative minimum.
-- source:
--   Kyprianou (2006), Lemma 3.5; uniform-grid reversal proof.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfDuality_finiteExtremaAlgebra
    {ι : Type} [Finite ι] [Nonempty ι] (v : ι → ℝ) (c : ℝ) :
    sSup (Set.range (fun i => v i - c)) = sSup (Set.range v) - c ∧
    sSup (Set.range (fun i => -v i)) = -sInf (Set.range v) := by sorry
