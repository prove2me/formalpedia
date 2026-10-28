-- Prove2me | Theorems.Thm_OAI_Mahler_source_regular_massBelow_of_flux_limit
-- name    : OAI.Mahler.source_regular_massBelow_of_flux_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:42:46.929423+00:00
-- url     : https://prove2.me/theorems/93a22caa-b632-441c-a6e6-e97c55604b92
-- title:
--   OAI.Mahler.source_regular_massBelow_of_flux_limit: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Mahler.source_regular_massBelow_of_flux_limit` of [lean/OAI/Analysis/Mahler/Mahler/SourceRegularMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/SourceRegularMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Mahler`, with `open Set MeasureTheory Filter MahlerStokes`, `open scoped Topology ENNReal`):
--
--   ```lean
--   theorem source_regular_massBelow_of_flux_limit (h : MassHypotheses (k+1) N m U f G)
--       {R L : ℝ} (hR : 0 < R) (hR1 : R < 1)
--       (hreg : ∀ z ∈ U, tau f z = R → fderiv ℝ (tau f) z ≠ 0)
--       (hlimit : Tendsto
--         (fun r => _root_.OAI.MahlerStokes.sphereFlux r (sourceCoordinateForm (sourceCoordinates k) (logTau f) k))
--         (𝓝[>] (0 : ℝ)) (𝓝 L)) :
--       ENNReal.ofReal (R^(k+1) * L) ≤ massBelow U f R
--   ```
--
--   **Definitions.** The statement is written with `OAI.Mahler.ComplexEuclidean`, `OAI.Mahler.MassHypotheses`, `OAI.Mahler.logTau`, `OAI.Mahler.massBelow`, `OAI.Mahler.sourceCoordinateForm`, `OAI.Mahler.sourceCoordinates`, `OAI.Mahler.tau` and `OAI.MahlerStokes.sphereFlux` (definitions bundle `OAISMh000` of this split).
--
--   **Used by.** The proof of `OAI.SymmetricMahler.symmetric_mahler` of this split imports it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/SourceRegularMass.lean (declaration OAI.Mahler.source_regular_massBelow_of_flux_limit)

import Mathlib
import Definitions.Def_OAISMh000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter MahlerStokes
open scoped Topology ENNReal
namespace Mahler
noncomputable section
variable {k N m : ℕ} {U : Set (ComplexEuclidean (k+1))}
  {f : Fin N → ComplexEuclidean (k+1) → ℂ} {G : Fin N → MvPolynomial (Fin (k+1)) ℂ}

theorem source_regular_massBelow_of_flux_limit (h : MassHypotheses (k+1) N m U f G)
    {R L : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ z ∈ U, tau f z = R → fderiv ℝ (tau f) z ≠ 0)
    (hlimit : Tendsto
      (fun r => _root_.OAI.MahlerStokes.sphereFlux r (sourceCoordinateForm (sourceCoordinates k) (logTau f) k))
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ENNReal.ofReal (R^(k+1) * L) ≤ massBelow U f R := by
  sorry

end
end Mahler

end OAI
end
