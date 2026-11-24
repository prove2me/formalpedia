-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_jacobian
-- name    : FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_jacobian
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:49.86137+00:00
-- url     : https://prove2.me/theorems/68344eb8-b052-4002-bae3-3bbdc2a2587b
-- title:
--   Embedded Resolution: graph Pre Submersive Presentation jacobian
-- statement:
--   The Embedded Resolution construction uses the graph Pre Submersive Presentation jacobian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebra.lean#L242-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebra.lean#L242-L255

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

theorem FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_jacobian [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).jacobian
      = (-1 : GraphAlgebra f) ^ Fintype.card τ * graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det := by sorry
