-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_jacobiMatrix
-- name    : FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_jacobiMatrix
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:36.096283+00:00
-- url     : https://prove2.me/theorems/ef79db1a-5df3-46a1-bff8-f7d611346677
-- title:
--   Embedded Resolution: graph Pre Submersive Presentation jacobi Matrix
-- statement:
--   The Embedded Resolution construction uses the graph Pre Submersive Presentation jacobi Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebra.lean#L231-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebra.lean#L231-L240

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

theorem FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_jacobiMatrix [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).jacobiMatrix
      = -((graphJacobianMinorMatrix f v).map
          (fun p => MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)) := by sorry
