-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_FirstJetGauge_transformedFirst_zero
-- name    : OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.transformedFirst_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:11:31.615202+00:00
-- url     : https://prove2.me/theorems/c38c2ed8-c80f-4a23-9365-e736d3398f0f
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.transformedFirst_zero: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.transformedFirst_zero` of [lean/OAI/Geometry/TamingCompatibility/Charts/FirstJetGauge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Charts/FirstJetGauge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge`, with `open scoped ContDiff RealInnerProductSpace`):
--
--   ```lean
--   lemma transformedFirst_zero [DecidableEq ι]
--       (q : ι → V →L[ℝ] ℝ) (e : ι → V)
--       (hqe : ∀ i j, q i (e j) = if i=j then 1 else 0)
--       (a : ι → ι → V → ℝ) (b : ι → V → End (W := W))
--       (ha : ∀ i j, a i j 0 = if i=j then 1 else 0) (j : ι) :
--       transformedFirst a b (OrthogonalJets.gauge (halfJet q (fun i => b i 0))) e j 0 = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.End`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.halfJet`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.transformedFirst` and `OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.gauge` (definitions bundle `OAIQ239Tc003` of this split).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedFirst_center` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Charts/FirstJetGauge.lean (declaration OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.transformedFirst_zero)

import Mathlib
import Definitions.Def_OAIQ239Tc003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FirstJetGauge
open scoped ContDiff RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma transformedFirst_zero [DecidableEq ι]
    (q : ι → V →L[ℝ] ℝ) (e : ι → V)
    (hqe : ∀ i j, q i (e j) = if i=j then 1 else 0)
    (a : ι → ι → V → ℝ) (b : ι → V → End (W := W))
    (ha : ∀ i j, a i j 0 = if i=j then 1 else 0) (j : ι) :
    transformedFirst a b (OrthogonalJets.gauge (halfJet q (fun i => b i 0))) e j 0 = 0 := by
  sorry

end TamingCompatibility.GeometricHilbert.FirstJetGauge

end

end OAI
end
