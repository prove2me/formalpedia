-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_OrthogonalJets_gauge_contDiff
-- name    : OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.gauge_contDiff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:11:41.006549+00:00
-- url     : https://prove2.me/theorems/1b0e8016-7b3e-48e9-825e-d3c8224c34a4
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.gauge_contDiff: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.gauge_contDiff` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/SymbolMap.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/SymbolMap.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets`, with `open scoped RealInnerProductSpace ContDiff`):
--
--   ```lean
--   lemma gauge_contDiff (A : V →L[ℝ] End (W := W)) : ContDiff ℝ ∞ (gauge A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.End` and `OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.gauge` (definitions bundle `OAIQ239Tc003` of this split).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoff_form_weak_deriv`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/SymbolMap.lean (declaration OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.gauge_contDiff)

import Mathlib
import Definitions.Def_OAIQ239Tc003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.OrthogonalJets
open scoped RealInnerProductSpace ContDiff
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma gauge_contDiff (A : V →L[ℝ] End (W := W)) : ContDiff ℝ ∞ (gauge A) := by
  sorry

end TamingCompatibility.GeometricHilbert.OrthogonalJets

end

end OAI
end
