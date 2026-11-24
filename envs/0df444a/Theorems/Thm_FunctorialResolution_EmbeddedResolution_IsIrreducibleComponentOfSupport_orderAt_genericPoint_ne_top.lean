-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_orderAt_genericPoint_ne_top
-- name    : FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport.orderAt_genericPoint_ne_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:58:33.953528+00:00
-- url     : https://prove2.me/theorems/a65b0eb2-8c0f-4058-a7c5-15e34e5804be
-- title:
--   Is Irreducible Component Of Support: order At generic Point ne top
-- statement:
--   The Is Irreducible Component Of Support construction uses the order At generic Point ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IrreducibleComponentsOfSupport.lean#L265-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IrreducibleComponentsOfSupport.lean#L265-L268

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}

theorem FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport.orderAt_genericPoint_ne_top [IsLocallyNoetherian X] (hC : IsIrreducibleComponentOfSupport D C)
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I) :
    orderAt I hC.isIrreducible.genericPoint ≠ ⊤ := by sorry
