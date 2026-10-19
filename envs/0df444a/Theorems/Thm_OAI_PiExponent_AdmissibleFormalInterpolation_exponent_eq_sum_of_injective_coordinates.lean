-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_exponent_eq_sum_of_injective_coordinates
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.exponent_eq_sum_of_injective_coordinates
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:21:24.749289+00:00
-- url     : https://prove2.me/theorems/a43dd4b6-4e5d-4a9b-a80a-8f60f60d24d8
-- title:
--   Identify a finitely supported exponent from its coordinates
-- statement:
--   A finitely supported exponent with the specified values at each injective coordinate, value zero at the disjoint base coordinate, and value zero elsewhere equals the sum of its coordinate singletons.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.exponent_eq_sum_of_injective_coordinates
    {σ : Type*} [DecidableEq σ] {m : ℕ}
    (v : Fin m → σ) (x0 : σ)
    (hv : Function.Injective v)
    (hdisj : ∀ i : Fin m, v i ≠ x0)
    (e : Fin m → ℕ) (d : σ →₀ ℕ)
    (hbase : d x0 = 0)
    (hcoord : ∀ i : Fin m, d (v i) = e i)
    (hout : ∀ x : σ, x ≠ x0 → (∀ i : Fin m, v i ≠ x) → d x = 0) :
    d = ∑ i : Fin m, Finsupp.single (v i) (e i) := by sorry
