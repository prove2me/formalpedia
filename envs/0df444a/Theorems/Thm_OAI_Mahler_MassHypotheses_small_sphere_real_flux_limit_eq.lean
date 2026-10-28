-- Prove2me | Theorems.Thm_OAI_Mahler_MassHypotheses_small_sphere_real_flux_limit_eq
-- name    : OAI.Mahler.MassHypotheses.small_sphere_real_flux_limit_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:23:35.764915+00:00
-- url     : https://prove2.me/theorems/0484eafa-a7f1-4d75-920b-58eb4a4a9c29
-- title:
--   OAI.Mahler.MassHypotheses.small_sphere_real_flux_limit_eq: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler_equality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Mahler.MassHypotheses.small_sphere_real_flux_limit` of [lean/OAI/Analysis/Mahler/Mahler/SphereDensityBridge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/SphereDensityBridge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Mahler`, with `open scoped BigOperators TensorProduct`, `open MeasureTheory Metric`):
--
--   ```lean
--   theorem MassHypotheses.small_sphere_real_flux_limit_eq {k N m : ℕ}
--       {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
--       {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
--       Filter.Tendsto (fun r => (radiusSphereFlux k (logTau f) r).re)
--         (nhdsWithin 0 (Set.Ioi 0)) (nhds (homogeneousSphereFlux k N G))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Mahler.ComplexEuclidean`, `OAI.Mahler.MassHypotheses`, `OAI.Mahler.homogeneousSphereFlux`, `OAI.Mahler.logTau` and `OAI.Mahler.radiusSphereFlux` (definitions bundle `OAIQ2Ma000` of this split).
--
--   **Used by.** The proofs of `OAI.Mahler.MassHypotheses.homogeneousFlux_endpoints_of_transgression_eq` and `OAI.Mahler.MassHypotheses.sourceCoordinateFlux_limit_eq` of this split import it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/SphereDensityBridge.lean (declaration OAI.Mahler.MassHypotheses.small_sphere_real_flux_limit)

import Mathlib
import Definitions.Def_OAIQ2Ma000

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators TensorProduct
open MeasureTheory Metric

namespace Mahler

theorem MassHypotheses.small_sphere_real_flux_limit_eq {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Filter.Tendsto (fun r => (radiusSphereFlux k (logTau f) r).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (homogeneousSphereFlux k N G)) := by
  sorry

end Mahler

end OAI
end
