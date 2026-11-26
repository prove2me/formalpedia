-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
-- name    : FourierJacobi.Valuations.actualEntryInteger_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:33:12.997806+00:00
-- url     : https://prove2.me/theorems/71f07335-b66e-5ac6-9f81-812758767662
-- title:
--   Valuations: actual Entry Integer coe
-- statement:
--   The Valuations construction uses the actual Entry Integer coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L57-L60
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean#L57-L60

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

theorem FourierJacobi.Valuations.actualEntryInteger_coe (v : AddValuation K (WithTop ℤ))
    (a : Kˣ) (x y z : K) :
    (actualEntryInteger v a x y z : WithTop ℤ) = matrixMinimum v (g a x y z) := by sorry
