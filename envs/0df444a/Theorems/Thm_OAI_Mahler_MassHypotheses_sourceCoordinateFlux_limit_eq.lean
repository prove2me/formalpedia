-- Prove2me | Theorems.Thm_OAI_Mahler_MassHypotheses_sourceCoordinateFlux_limit_eq
-- name    : OAI.Mahler.MassHypotheses.sourceCoordinateFlux_limit_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:23:54.597909+00:00
-- url     : https://prove2.me/theorems/96014e75-68b3-4c0f-b453-af76e6f7821a
-- title:
--   OAI.Mahler.MassHypotheses.sourceCoordinateFlux_limit_eq: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler_equality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Mahler.MassHypotheses.sourceCoordinateFlux_limit` of [lean/OAI/Analysis/Mahler/Mahler/SourceRadiusFlux.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/SourceRadiusFlux.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Mahler`, with `open Set Metric MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem MassHypotheses.sourceCoordinateFlux_limit_eq {k N m : ℕ}
--       {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
--       {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
--       Tendsto (fun r => MahlerStokes.sphereFlux r
--         (sourceCoordinateForm (sourceCoordinates k) (logTau f) k))
--         (𝓝[>] 0) (𝓝 (homogeneousSphereFlux k N G))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Mahler.ComplexEuclidean`, `OAI.Mahler.MassHypotheses`, `OAI.Mahler.homogeneousSphereFlux`, `OAI.Mahler.logTau`, `OAI.Mahler.sourceCoordinateForm`, `OAI.Mahler.sourceCoordinates` and `OAI.MahlerStokes.sphereFlux` (definitions bundle `OAIQ2Ma000` of this split).
--
--   **Used by.** The proof of `OAI.SymmetricMahler.equality_strip_images_dense_eq` of this split imports it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/SourceRadiusFlux.lean (declaration OAI.Mahler.MassHypotheses.sourceCoordinateFlux_limit)

import Mathlib
import Definitions.Def_OAIQ2Ma000

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology
namespace Mahler

theorem MassHypotheses.sourceCoordinateFlux_limit_eq {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Tendsto (fun r => MahlerStokes.sphereFlux r
      (sourceCoordinateForm (sourceCoordinates k) (logTau f) k))
      (𝓝[>] 0) (𝓝 (homogeneousSphereFlux k N G)) := by
  sorry

end Mahler

end

end OAI
end
