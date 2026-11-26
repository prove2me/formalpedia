-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actualInteger_bounds
-- name    : FourierJacobi.Valuations.actualInteger_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:59.79729+00:00
-- url     : https://prove2.me/theorems/1b6e9f8f-e42f-581d-a019-293d46573411
-- title:
--   Valuations: actual Integer bounds
-- statement:
--   The Valuations construction uses the actual Integer bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L68-L84
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L68-L84

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable {K : Type*} [Field K]

theorem FourierJacobi.Valuations.actualInteger_bounds (v : AddValuation K (WithTop ℤ))
    (a : Kˣ) (x y z : K) :
    2 * actualEntryInteger v a x y z ≤ actualMinorInteger v a x y z ∧
    actualMinorInteger v a x y z ≤ actualEntryInteger v a x y z ∧
    actualEntryInteger v a x y z ≤ 0 := by sorry
