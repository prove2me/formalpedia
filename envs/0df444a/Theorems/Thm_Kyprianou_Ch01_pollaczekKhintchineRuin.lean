-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pollaczekKhintchineRuin
-- name    : Kyprianou.Ch01.pollaczekKhintchineRuin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:12:34.544551+00:00
-- url     : https://prove2.me/theorems/0a5ff3b4-2dcc-4e36-b1fd-0fba07a74bd9
-- title:
--   Theorem 1.8: Pollaczek–Khintchine survival series in the Cramér–Lundberg model
-- statement:
--   Theorem 1.8 uses the actual strict-ruin event and conditional deficit law η at initial surplus zero, characterised by a joint-event identity. It proves the entire survival series in x, with its zero-capital ruin probability as the series weight; the parameter ρ is not assumed equal to λμ/c in this result. Draft declaration, not a proof; remote elaboration and source type audit pending.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Theorem 1.8, p. 17, equation (1.11).

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.pollaczekKhintchineRuin
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (premium : ℝ) (hpremium : 0 < premium)
    (hnet : (rate : ℝ) * mu < premium)
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hetaSupport : eta (Set.Iio (0 : ℝ)) = 0)
    (heta : ∀ x : ℝ, 0 ≤ x →
      (P (ruinEvent arrival claims premium 0 ∩
        {ω | ruinDeficit arrival claims premium 0 ω ≤ x})).toReal =
        ruinProbability P arrival claims premium 0 *
          (eta (Set.Iic x)).toReal) :
    ∀ x : ℝ, 0 ≤ x →
      1 - ruinProbability P arrival claims premium x =
        pkCDF eta (ruinProbability P arrival claims premium 0) x := by
  sorry
