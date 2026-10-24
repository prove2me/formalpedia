-- Prove2me | Theorems.Thm_OAI_PiExponent_logarithmic_interpolation_volume_bounds_of_eventual
-- name    : OAI.PiExponent.logarithmic_interpolation_volume_bounds_of_eventual
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T16:58:39.521437+00:00
-- url     : https://prove2.me/theorems/01a5a6c1-d8a8-4870-a4af-a44060f67fcb
-- title:
--   Necessary volume bounds for eventual logarithmic interpolation
-- statement:
--   If one threshold rule gives eventual interpolation for every positive weight vector and every coordinatewise-distinct center family at contraction alpha, then the transverse and full weighted volume ratios are at most one. Restricting jet data to time degree zero gives the transverse bound; counting all jet data gives the full bound. The conclusion is weak because asymptotic dimension counting does not give strictness.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup

open scoped BigOperators

theorem OAI.PiExponent.logarithmic_interpolation_volume_bounds_of_eventual
    (m K : ℕ) (hm : 0 < m) (hK : 0 < K)
    (w0 v0 alpha : ℚ) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hbase :
      ∃ S : List ℕ → ℕ,
        ∀ w : Fin m → ℕ, (∀ i, 0 < w i) →
          OAI.PiExponent.separatedWeights S w →
          ∀ c : Fin K → Fin m → ℂ,
            (∀ i : Fin m, Function.Injective (fun j : Fin K => c j i)) →
            OAI.PiExponent.eventualLogJetSurjective m K w0 v0 alpha w c) :
    (K : ℚ) * alpha ^ m ≤ 1 ∧
      (K : ℚ) * (w0 / v0) * alpha ^ m ≤ 1 := by sorry
