-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lundbergAsymptotic
-- name    : Kyprianou.Ch01.lundbergAsymptotic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:13:58.202722+00:00
-- url     : https://prove2.me/theorems/41747eee-3d1b-40c3-8389-59e9ff2104f2
-- title:
--   Theorem 1.10(ii): Cramér non-lattice asymptotic ruin probability
-- statement:
--   Preserves the extra non-lattice condition. Its asymptotic constant is the reciprocal of the coefficient (λν/(c−λμ)) times the exponentially weighted integrated claim tail; by the book's convention it is zero when the integral diverges. Draft declaration, not a proof; remote elaboration and source type audit pending.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Theorem 1.10, pp. 17–18, second assertion.

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.lundbergAsymptotic
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
    (nu : ℝ) (hnu : 0 < nu)
    (hnonlattice : IsNonLattice F)
    (hint : Integrable
      (fun ω => Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω)) P)
    (hroot : (∫ ω, Real.exp
      (-nu * riskSurplus arrival claims premium 0 1 ω) ∂P) = 1) :
    let weightedTail : ℝ≥0∞ :=
      ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal
          (y * Real.exp (nu * y) * (F (Set.Ioi y)).toReal) ∂volume
    Tendsto (fun x : ℝ => Real.exp (nu * x) *
      ruinProbability P arrival claims premium x) atTop
      (nhds (if weightedTail = ⊤ then 0 else
        (((rate : ℝ) * nu / (premium - (rate : ℝ) * mu)) *
          weightedTail.toReal)⁻¹)) := by
  sorry
