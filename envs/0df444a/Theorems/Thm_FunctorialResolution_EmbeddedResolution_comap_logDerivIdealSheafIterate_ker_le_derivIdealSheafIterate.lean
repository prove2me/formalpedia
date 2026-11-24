-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate
-- name    : FunctorialResolution.EmbeddedResolution.comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:37:14.770436+00:00
-- url     : https://prove2.me/theorems/8407b4b1-a0a2-4165-8c0e-274d36fe5b7f
-- title:
--   Embedded Resolution: comap log Deriv Ideal Sheaf Iterate ker le deriv Ideal Sheaf Iterate
-- statement:
--   The Embedded Resolution construction uses the comap log Deriv Ideal Sheaf Iterate ker le deriv Ideal Sheaf Iterate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheafClosedSubscheme.lean#L121-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheafClosedSubscheme.lean#L121-L128

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheafClosedSubscheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) := by sorry
