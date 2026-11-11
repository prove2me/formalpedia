-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalJets_pullbackMetric_scalar_hasFDerivAt_zero
-- name    : OAI.TamingCompatibility.GeometricHilbert.NormalJets.pullbackMetric_scalar_hasFDerivAt_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:12:04.479725+00:00
-- url     : https://prove2.me/theorems/c99e72a0-4803-4193-8a55-680ef751e60b
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.NormalJets.pullbackMetric_scalar_hasFDerivAt_zero: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.NormalJets.pullbackMetric_scalar_hasFDerivAt_zero` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/MetricTensor.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/MetricTensor.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.NormalJets`, with `open scoped RealInnerProductSpace ContDiff`):
--
--   ```lean
--   lemma pullbackMetric_scalar_hasFDerivAt_zero (g : V → MetricTensor (V := V))
--       (G : MetricDerivative (V := V)) (hg : HasFDerivAt g G 0)
--       (hg0 : g 0 = innerSL ℝ) (hG : ∀ u v w, G u v w = G u w v) (v w : V) :
--       HasFDerivAt (fun z => pullbackMetric g G z v w) (0 : V →L[ℝ] ℝ) 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricDerivative`, `OAI.TamingCompatibility.GeometricHilbert.NormalJets.MetricTensor` and `OAI.TamingCompatibility.GeometricHilbert.NormalJets.pullbackMetric` (definitions bundle `OAIQ239Tc003` of this split).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMetric_dpos_zero` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/MetricTensor.lean (declaration OAI.TamingCompatibility.GeometricHilbert.NormalJets.pullbackMetric_scalar_hasFDerivAt_zero)

import Mathlib
import Definitions.Def_OAIQ239Tc003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open scoped RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma pullbackMetric_scalar_hasFDerivAt_zero (g : V → MetricTensor (V := V))
    (G : MetricDerivative (V := V)) (hg : HasFDerivAt g G 0)
    (hg0 : g 0 = innerSL ℝ) (hG : ∀ u v w, G u v w = G u w v) (v w : V) :
    HasFDerivAt (fun z => pullbackMetric g G z v w) (0 : V →L[ℝ] ℝ) 0 := by
  sorry

end TamingCompatibility.GeometricHilbert.NormalJets

end

end OAI
end
