-- Prove2me | Theorems.Thm_OAI_Mahler_source_punctured_scaled_extDeriv_eq
-- name    : OAI.Mahler.source_punctured_scaled_extDeriv_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:22:19.42973+00:00
-- url     : https://prove2.me/theorems/afffe260-c21d-401f-bb4d-02157c7433a9
-- title:
--   OAI.Mahler.source_punctured_scaled_extDeriv_eq: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler_equality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Mahler.source_punctured_scaled_extDeriv` of [lean/OAI/Analysis/Mahler/Mahler/SourceBoundaryIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/SourceBoundaryIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Mahler`, with `open Set Filter MeasureTheory ContinuousAlternatingMap MahlerStokes`, `open scoped Topology Manifold`):
--
--   ```lean
--   theorem source_punctured_scaled_extDeriv_eq (h : MassHypotheses n N m U f G) (k : ℕ)
--       (Ψ : (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
--       {R r : ℝ} (hR : 0 < R) (hR1 : R < 1)
--       (hreg : ∀ x ∈ U, tau f x = R → fderiv ℝ (tau f) x ≠ 0)
--       (hr : 0 < r)
--       (hB : coordClosedBall ((2*k+1)+1) r ⊆ regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R) :
--       (R⁻¹)^(k+1) *
--         (∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R,
--           extDeriv (sourceCoordinateForm Ψ (energy f) k) x (coordinateBasis ((2*k+1)+1))) -
--         _root_.OAI.MahlerStokes.sphereFlux r (sourceCoordinateForm Ψ (logTau f) k) =
--         ∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R \ coordClosedBall ((2*k+1)+1) r,
--           extDeriv (sourceCoordinateForm Ψ (logTau f) k) x (coordinateBasis ((2*k+1)+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Mahler.ComplexEuclidean`, `OAI.Mahler.MassHypotheses`, `OAI.Mahler.energy`, `OAI.Mahler.logTau`, `OAI.Mahler.sourceCoordinateForm`, `OAI.Mahler.tau`, `OAI.MahlerStokes.coordClosedBall`, `OAI.MahlerStokes.coordinateBasis`, `OAI.MahlerStokes.regularSublevel` and `OAI.MahlerStokes.sphereFlux` (definitions bundle `OAIQ2Ma000` of this split).
--
--   **Used by.** The proof of `OAI.Mahler.source_regular_massBelow_of_flux_limit_eq` of this split imports it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/SourceBoundaryIntegral.lean (declaration OAI.Mahler.source_punctured_scaled_extDeriv)

import Mathlib
import Definitions.Def_OAIQ2Ma000

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory ContinuousAlternatingMap MahlerStokes
open scoped Topology Manifold

namespace Mahler
noncomputable section
variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

theorem source_punctured_scaled_extDeriv_eq (h : MassHypotheses n N m U f G) (k : ℕ)
    (Ψ : (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
    {R r : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ x ∈ U, tau f x = R → fderiv ℝ (tau f) x ≠ 0)
    (hr : 0 < r)
    (hB : coordClosedBall ((2*k+1)+1) r ⊆ regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R) :
    (R⁻¹)^(k+1) *
      (∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R,
        extDeriv (sourceCoordinateForm Ψ (energy f) k) x (coordinateBasis ((2*k+1)+1))) -
      _root_.OAI.MahlerStokes.sphereFlux r (sourceCoordinateForm Ψ (logTau f) k) =
      ∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R \ coordClosedBall ((2*k+1)+1) r,
        extDeriv (sourceCoordinateForm Ψ (logTau f) k) x (coordinateBasis ((2*k+1)+1)) := by
  sorry

end
end Mahler

end OAI
end
