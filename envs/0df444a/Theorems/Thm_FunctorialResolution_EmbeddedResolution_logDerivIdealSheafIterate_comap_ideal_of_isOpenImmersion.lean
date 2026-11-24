-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion
-- name    : FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:36:57.472043+00:00
-- url     : https://prove2.me/theorems/23a76bc7-7186-4797-9a33-f956553aac1b
-- title:
--   Embedded Resolution: log Deriv Ideal Sheaf Iterate comap ideal of is Open Immersion
-- statement:
--   The Embedded Resolution construction uses the log Deriv Ideal Sheaf Iterate comap ideal of is Open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheafOpenImmersion.lean#L106-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheafOpenImmersion.lean#L106-L120

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheafOpenImmersion
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
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
  (g : Y ⟶ X) [IsOpenImmersion g] [LocallyOfFiniteType (g ≫ p)]

theorem FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion
    (P A : X.IdealSheafData) (r : ℕ) (V : Y.affineOpens) :
    ((logDerivIdealSheafIterate k p P r A).comap g).ideal V =
      (logDerivIdealSheafIterate k (g ≫ p) (P.comap g) r (A.comap g)).ideal V := by sorry
