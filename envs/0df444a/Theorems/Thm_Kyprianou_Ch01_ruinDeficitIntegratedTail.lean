-- Prove2me | Theorems.Thm_Kyprianou_Ch01_ruinDeficitIntegratedTail
-- name    : Kyprianou.Ch01.ruinDeficitIntegratedTail
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:12:59.688636+00:00
-- url     : https://prove2.me/theorems/66d25383-1666-4029-b589-cc8ba48e0ffd
-- title:
--   Theorem 1.9: initial ruin probability and integrated-tail deficit law
-- statement:
--   Theorem 1.9 identifies both unknowns in the Pollaczek–Khintchine formula: the probability of ruin from zero, and the conditional first-ruin deficit CDF as the normalized integrated tail of the claim law. The joint-event identity avoids division by a conditional probability; it is equivalent when the zero-capital ruin probability is positive. Draft declaration, not a proof; remote elaboration and source type audit pending.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Theorem 1.9, p. 17, equation (1.12).

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.ruinDeficitIntegratedTail
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
    (hnet : (rate : ℝ) * mu < premium) :
    ruinProbability P arrival claims premium 0 =
        (rate : ℝ) * mu / premium ∧
      ∀ x : ℝ, 0 ≤ x →
        (P (ruinEvent arrival claims premium 0 ∩
          {ω | ruinDeficit arrival claims premium 0 ω ≤ x})).toReal =
          ruinProbability P arrival claims premium 0 *
            integratedTailCDF F mu x := by
  sorry
