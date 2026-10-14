-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finite_linear_functionals_interpolation
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.finite_linear_functionals_interpolation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T09:27:36.947978+00:00
-- url     : https://prove2.me/theorems/cb427db3-5785-4ebf-8275-2e0ff68af09e
-- title:
--   Interpolation by independent linear functionals
-- statement:
--   For a finite family of linearly independent scalar-valued linear functionals, there are vectors on which the functionals have Kronecker-delta values.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.LinearAlgebra.LinearIndependent.Basic

theorem OAI.PiExponent.AdmissibleFormalInterpolation.finite_linear_functionals_interpolation
    {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι]
    (f : ι → V →ₗ[K] K) (hf : LinearIndependent K f) :
    ∃ q : ι → V, ∀ i j, f i (q j) = if i = j then 1 else 0 := by sorry
