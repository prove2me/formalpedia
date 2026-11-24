-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_comp_eq_imageIdealSheaf_ker
-- name    : FunctorialResolution.EmbeddedResolution.ker_comp_eq_imageIdealSheaf_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:22.667645+00:00
-- url     : https://prove2.me/theorems/6cb7d36d-7135-433f-98f0-5ab8aa2455a2
-- title:
--   Embedded Resolution: ker comp eq image Ideal Sheaf ker
-- statement:
--   The Embedded Resolution construction uses the ker comp eq image Ideal Sheaf ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L43-L46

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.ker_comp_eq_imageIdealSheaf_ker {W A B : Scheme.{u}} (g : W ⟶ A) (w : A ⟶ B) :
    (g ≫ w).ker = imageIdealSheaf w g.ker := by sorry
