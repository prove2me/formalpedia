-- Prove2me | Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_isNormalScheme_spec
-- name    : GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:27:06.925637+00:00
-- url     : https://prove2.me/theorems/e06a273a-99d1-5dd4-b304-0fbbbdb74479
-- title:
--   Semi Abelian Hom Extension: is Normal Scheme spec
-- statement:
--   The Semi Abelian Hom Extension construction uses the is Normal Scheme spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L571-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L571-L583

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}

theorem GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := by sorry
