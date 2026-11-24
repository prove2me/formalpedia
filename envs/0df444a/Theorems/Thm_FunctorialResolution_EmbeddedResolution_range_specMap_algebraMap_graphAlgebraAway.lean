-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_range_specMap_algebraMap_graphAlgebraAway
-- name    : FunctorialResolution.EmbeddedResolution.range_specMap_algebraMap_graphAlgebraAway
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:59:52.035565+00:00
-- url     : https://prove2.me/theorems/a044d736-cc33-47c3-89df-61aebe94e72f
-- title:
--   Embedded Resolution: range spec Map algebra Map graph Algebra Away
-- statement:
--   The Embedded Resolution construction uses the range spec Map algebra Map graph Algebra Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebraSpecSmooth.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebraSpecSmooth.lean#L39-L46

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraStandardSmooth
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraSpecSmooth
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
open CategoryTheory AlgebraicGeometry
variable {R : Type u} [CommRing R] {σ τ : Type u} [Fintype τ] [DecidableEq τ]

theorem FunctorialResolution.EmbeddedResolution.range_specMap_algebraMap_graphAlgebraAway
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Set.range ⇑(Spec.map
        (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))).base =
      (PrimeSpectrum.basicOpen (graphJacobianMinorDet f v) : Set (PrimeSpectrum (GraphAlgebra f))) := by sorry
