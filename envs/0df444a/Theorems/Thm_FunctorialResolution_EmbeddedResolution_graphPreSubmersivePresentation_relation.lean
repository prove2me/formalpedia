-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_relation
-- name    : FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_relation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:02.240861+00:00
-- url     : https://prove2.me/theorems/6a2c2d89-6ea4-4fc1-883d-9a328c6d1c3d
-- title:
--   Embedded Resolution: graph Pre Submersive Presentation relation
-- statement:
--   The Embedded Resolution construction uses the graph Pre Submersive Presentation relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebra.lean#L214-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebra.lean#L214-L217

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

theorem FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_relation (f : τ → MvPolynomial σ R) (v : τ → σ)
    (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).relation = graphRelation f := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_relation
