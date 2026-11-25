-- Prove2me | Theorems.Thm_GlobalTheory_IsGenericPointHom_quasiCompact_and_dominant
-- name    : GlobalTheory.IsGenericPointHom.quasiCompact_and_dominant
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:36.691953+00:00
-- url     : https://prove2.me/theorems/f6bb9917-e62b-41d4-a3a0-41efc9349727
-- title:
--   Is Generic Point Hom: quasi Compact and dominant
-- statement:
--   The Is Generic Point Hom construction uses the quasi Compact and dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L279-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L279-L281

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_quasiCompact_and_dominant

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
open GlobalTheory
open ExtUnique
open GlobalTheory.IsGenericPointHom
variable {U S : Scheme.{u}} [IsIntegral S] {j : U ⟶ S}

theorem GlobalTheory.IsGenericPointHom.quasiCompact_and_dominant [IsLocallyNoetherian S] (hj : IsGenericPointHom j) :
    QuasiCompact j ∧ IsSchemeTheoreticallyDominant j := by sorry
