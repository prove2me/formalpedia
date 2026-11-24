-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_formallySmooth_residueField
-- name    : FunctorialResolution.EmbeddedResolution.formallySmooth_residueField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:17:25.45669+00:00
-- url     : https://prove2.me/theorems/85bfb692-9060-4c48-b9cb-1d3c270ef6b1
-- title:
--   Embedded Resolution: formally Smooth residue Field
-- statement:
--   The Embedded Resolution construction uses the formally Smooth residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheafOrderDecrease.lean#L306-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheafOrderDecrease.lean#L306-L312

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
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

theorem FunctorialResolution.EmbeddedResolution.formallySmooth_residueField (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X)
    [Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk x))]
    (_h : algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) =
      (IsLocalRing.residue (X.presheaf.stalk x)).comp (stalkAlgebraMap k p x)) :
    Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by sorry
