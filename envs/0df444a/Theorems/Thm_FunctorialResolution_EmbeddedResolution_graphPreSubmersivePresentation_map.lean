-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_map
-- name    : FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:06.103805+00:00
-- url     : https://prove2.me/theorems/97bc07ef-ec3a-4b7b-9168-ec9a045112ad
-- title:
--   Embedded Resolution: graph Pre Submersive Presentation map
-- statement:
--   The Embedded Resolution construction uses the graph Pre Submersive Presentation map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebra.lean#L219-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebra.lean#L219-L222

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

theorem FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_map (f : τ → MvPolynomial σ R) (v : τ → σ)
    (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).map = v := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_map
