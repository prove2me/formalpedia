-- Prove2me | Theorems.Thm_GlobalTheory_GroupRingConst_pt_comp_family
-- name    : GlobalTheory.GroupRingConst.pt_comp_family
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:40.133269+00:00
-- url     : https://prove2.me/theorems/2fa7b12a-75ae-43a5-a7ef-e0ec4de551df
-- title:
--   Group Ring Const: pt comp family
-- statement:
--   The Group Ring Const construction uses the pt comp family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GroupRingHomConstOfLaurent.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GroupRingHomConstOfLaurent.lean#L73-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GroupRingConst

theorem GlobalTheory.GroupRingConst.pt_comp_family {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (r : R →+* F) (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) (u : Fˣ) :
    (pt (RingHom.id F) (zpowersHom Fˣ u)).comp (family r c l) = pt r (c * powChar l u) := by sorry
