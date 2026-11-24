-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isStandardSmooth_graphAlgebraAway
-- name    : FunctorialResolution.EmbeddedResolution.isStandardSmooth_graphAlgebraAway
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:09.015123+00:00
-- url     : https://prove2.me/theorems/74b0288f-b52c-409a-84b0-f8b59d0137c9
-- title:
--   Embedded Resolution: is Standard Smooth graph Algebra Away
-- statement:
--   The Embedded Resolution construction uses the is Standard Smooth graph Algebra Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebraStandardSmooth.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebraStandardSmooth.lean#L61-L66

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraStandardSmooth
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

theorem FunctorialResolution.EmbeddedResolution.isStandardSmooth_graphAlgebraAway [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.IsStandardSmooth (MvPolynomial τ R) (GraphAlgebraAway f v) := by sorry
