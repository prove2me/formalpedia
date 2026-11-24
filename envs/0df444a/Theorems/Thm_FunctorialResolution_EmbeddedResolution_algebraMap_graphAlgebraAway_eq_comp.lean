-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_algebraMap_graphAlgebraAway_eq_comp
-- name    : FunctorialResolution.EmbeddedResolution.algebraMap_graphAlgebraAway_eq_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:59:37.315018+00:00
-- url     : https://prove2.me/theorems/b11a2d9f-881c-4f79-842f-7d7debd80480
-- title:
--   Embedded Resolution: algebra Map graph Algebra Away eq comp
-- statement:
--   The Embedded Resolution construction uses the algebra Map graph Algebra Away eq comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebraSpecSmooth.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebraSpecSmooth.lean#L48-L53

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

theorem FunctorialResolution.EmbeddedResolution.algebraMap_graphAlgebraAway_eq_comp
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)) =
      (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)).comp
        (algebraMap (MvPolynomial τ R) (GraphAlgebra f)) := by sorry
