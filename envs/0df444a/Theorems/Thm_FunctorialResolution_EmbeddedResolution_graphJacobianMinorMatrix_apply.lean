-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphJacobianMinorMatrix_apply
-- name    : FunctorialResolution.EmbeddedResolution.graphJacobianMinorMatrix_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:25:47.337385+00:00
-- url     : https://prove2.me/theorems/41d8f4ca-eeb8-4603-a906-3dd4b553faa2
-- title:
--   Embedded Resolution: graph Jacobian Minor Matrix apply
-- statement:
--   The Embedded Resolution construction uses the graph Jacobian Minor Matrix apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebra.lean#L227-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebra.lean#L227-L229

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {R : Type u} [CommRing R] {σ τ : Type u}
noncomputable section

theorem FunctorialResolution.EmbeddedResolution.graphJacobianMinorMatrix_apply (f : τ → MvPolynomial σ R) (v : τ → σ) (i j : τ) :
    graphJacobianMinorMatrix f v i j = MvPolynomial.pderiv (v i) (f j) := by sorry
