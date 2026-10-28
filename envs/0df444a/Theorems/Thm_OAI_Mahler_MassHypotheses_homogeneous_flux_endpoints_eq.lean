-- Prove2me | Theorems.Thm_OAI_Mahler_MassHypotheses_homogeneous_flux_endpoints_eq
-- name    : OAI.Mahler.MassHypotheses.homogeneous_flux_endpoints_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:21:17.837842+00:00
-- url     : https://prove2.me/theorems/1c1b141f-666b-4403-bfd3-9d91f0270fbe
-- title:
--   OAI.Mahler.MassHypotheses.homogeneous_flux_endpoints_eq: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler_equality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Mahler.MassHypotheses.homogeneous_flux_endpoints` of [lean/OAI/Analysis/Mahler/Mahler/HomogeneousEndpoint.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/HomogeneousEndpoint.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Mahler`, with `open Set Filter Metric`, `open scoped Topology`):
--
--   ```lean
--   theorem MassHypotheses.homogeneous_flux_endpoints_eq {k N m : ℕ}
--       {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
--       {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G) :
--       homogeneousSphereFlux (k+1) N G = (Real.pi*(m:ℝ))^(k+2) ∧
--       Tendsto (fun r => (radiusSphereFlux (k+1) (logTau f) r).re)
--         (𝓝[>] (0:ℝ)) (𝓝 ((Real.pi*(m:ℝ))^(k+2)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Mahler.ComplexEuclidean`, `OAI.Mahler.MassHypotheses`, `OAI.Mahler.homogeneousSphereFlux`, `OAI.Mahler.logTau` and `OAI.Mahler.radiusSphereFlux` (definitions bundle `OAIQ2Ma000` of this split).
--
--   **Used by.** The proof of `OAI.Mahler.MassHypotheses.homogeneousSphereFlux_value_eq` of this split imports it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/HomogeneousEndpoint.lean (declaration OAI.Mahler.MassHypotheses.homogeneous_flux_endpoints)

import Mathlib
import Definitions.Def_OAIQ2Ma000

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Mahler

theorem MassHypotheses.homogeneous_flux_endpoints_eq {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G) :
    homogeneousSphereFlux (k+1) N G = (Real.pi*(m:ℝ))^(k+2) ∧
    Tendsto (fun r => (radiusSphereFlux (k+1) (logTau f) r).re)
      (𝓝[>] (0:ℝ)) (𝓝 ((Real.pi*(m:ℝ))^(k+2))) := by
  sorry

end Mahler

end

end OAI
end
