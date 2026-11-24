-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_genericPoint_mem
-- name    : FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport.genericPoint_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:55:17.826586+00:00
-- url     : https://prove2.me/theorems/51b86c91-779f-44b5-a7ae-13a3fec1aa26
-- title:
--   Is Irreducible Component Of Support: generic Point mem
-- statement:
--   The Is Irreducible Component Of Support construction uses the generic Point mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IrreducibleComponentsOfSupport.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IrreducibleComponentsOfSupport.lean#L102-L106

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

theorem FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport.genericPoint_mem (hC : IsIrreducibleComponentOfSupport D C) :
    hC.isIrreducible.genericPoint ∈ C := by sorry
