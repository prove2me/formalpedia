-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_linearIndependent_of_kronecker_pairing
-- name    : OAI.PiExponent.LogarithmicJetIdeals.linearIndependent_of_kronecker_pairing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T09:06:03.009813+00:00
-- url     : https://prove2.me/theorems/64ec9115-8eeb-4b60-a06b-ec08abf0279b
-- title:
--   Linear independence from a Kronecker pairing
-- statement:
--   A finite family of linear functionals is linearly independent if there is a matching family of vectors on which their evaluations form the identity matrix.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.LinearAlgebra.LinearIndependent.Basic

theorem OAI.PiExponent.LogarithmicJetIdeals.linearIndependent_of_kronecker_pairing
    {K M ι : Type} [Field K] [AddCommMonoid M] [Module K M]
    [Fintype ι] [DecidableEq ι]
    (L : ι → M →ₗ[K] K) (v : ι → M)
    (h : ∀ i j, L i (v j) = if i = j then 1 else 0) :
    LinearIndependent K L := by sorry
