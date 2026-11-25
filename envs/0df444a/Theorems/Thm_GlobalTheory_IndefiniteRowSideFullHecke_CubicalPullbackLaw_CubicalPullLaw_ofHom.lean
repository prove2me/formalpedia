-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CubicalPullbackLaw_CubicalPullLaw_ofHom
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw.CubicalPullLaw.ofHom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:49.881684+00:00
-- url     : https://prove2.me/theorems/e6081058-75ac-5b0d-a778-7f0f0624e7b4
-- title:
--   Cubical Pull Law: of Hom
-- statement:
--   The Cubical Pull Law construction uses the of Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/CubicalPullbackLaw.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/CubicalPullbackLaw.lean#L56-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_CubicalPullbackLaw
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
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw

theorem GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw.CubicalPullLaw.ofHom (h : CubicalPullLaw) : CubicalPullOfHomSt.{0} := by sorry
