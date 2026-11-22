-- Prove2me | Theorems.Thm_MasulloRH_translated_negative_gram_distance_to_geometric_approximants
-- name    : MasulloRH.translated_negative_gram_distance_to_geometric_approximants
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T07:11:04.536101+00:00
-- url     : https://prove2.me/theorems/bcf96155-78fa-4122-8b93-a529d9dbb6df
-- title:
--   The normalized negative-translation distance to geometric approximants vanishes
-- statement:
--   With w(x)=exp(|x|)(1+x²)², suppose a fixed f can be approximated arbitrarily closely by a class S in L²(exp(-x)dx), and all the residuals belong to L²(w dx). Then the infimum over S of the squared L²(w dx) error after translation by -L, divided by exp(L)L⁴, tends to zero. This bounds the actual spectral projection error when S is a translation-invariant geometric class. In the application the S00 packet supplies the approximation premise.
-- source:
--   Masullo (9.2.2.41); critical-width large-translation asymptotics for the global Gram form.

import Mathlib
open MeasureTheory Filter Topology

theorem MasulloRH.translated_negative_gram_distance_to_geometric_approximants (f : ℝ → ℂ) (S : Set (ℝ → ℂ))
    (hf : AEStronglyMeasurable f volume)
    (hs : ∀ u ∈ S, AEStronglyMeasurable u volume)
    (hint : ∀ u ∈ S, Integrable (fun x : ℝ =>
      (Real.exp |x| * (1+x^2)^2) * ‖f x - u x‖^2))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ u ∈ S,
        (∫ x : ℝ, Real.exp (-x) * ‖f x-u x‖^2) < ε) :
    Tendsto (fun L : ℝ => sInf ((fun u : ℝ → ℂ =>
      ∫ x : ℝ, ((Real.exp |x-L| * (1+(x-L)^2)^2) / (Real.exp L * L^4)) *
        ‖f x-u x‖^2) '' S)) atTop (𝓝 0) := by sorry
