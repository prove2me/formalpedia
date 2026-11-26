-- Prove2me | Theorems.Thm_MassPosOfNonzero
-- name    : MassPosOfNonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:31.26981+00:00
-- url     : https://prove2.me/theorems/93bd5132-db58-444b-aa0c-34507f8aec82
-- title:
--   Mass Pos Of Nonzero: Mass Pos Of Nonzero
-- statement:
--   `𝕄(T) ≠ 0` for a nonzero functional: if the infimum over admissible measures were `0`, every
--   `T ω` would be forced to `0`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/MassPosOfNonzero.lean#L9-L39
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/MassPosOfNonzero.lean#L9-L39

import Definitions.Def_Tablet_massOfFunctional
import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_MassPosOfNonzero
set_option autoImplicit false
open MeasureTheory ENNReal

theorem MassPosOfNonzero {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (hT : T ≠ 0) : massOfFunctional T ≠ 0 := by sorry
