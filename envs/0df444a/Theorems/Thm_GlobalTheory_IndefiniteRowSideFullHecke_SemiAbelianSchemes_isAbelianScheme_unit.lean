-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianSchemes_isAbelianScheme_unit
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.isAbelianScheme_unit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:57.814303+00:00
-- url     : https://prove2.me/theorems/94dd1f84-d11f-4815-9ddb-10c4aa7eaa9e
-- title:
--   Semi Abelian Schemes: is Abelian Scheme unit
-- statement:
--   The Semi Abelian Schemes construction uses the is Abelian Scheme unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SemiAbelianSchemes.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SemiAbelianSchemes.lean#L45-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
open ReciprocityTheory.ChartRestriction.G.Semi

theorem GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.isAbelianScheme_unit (S : Scheme.{u}) : IsAbelianScheme (𝟙_ (Over S)) := by sorry
