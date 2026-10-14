-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_evaluationMap_surjective
-- name    : OAI.PiExponent.LogarithmicJetIdeals.evaluationMap_surjective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T09:12:37.45961+00:00
-- url     : https://prove2.me/theorems/680d01a7-09c9-4b31-85dd-617cd46a62c9
-- title:
--   Surjectivity of the finite coordinate evaluation map
-- statement:
--   For a finite linearly independent family of linear functionals, the map sending each vector to all its functional values is surjective onto the space of coordinate functions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_evaluationMap

theorem OAI.PiExponent.LogarithmicJetIdeals.evaluationMap_surjective
    {K V ι : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [AddCommGroup V] [Module K V]
    (L : ι → V →ₗ[K] K) (hL : LinearIndependent K L) :
    Function.Surjective (evaluationMap L) := by sorry
