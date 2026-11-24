-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianSchemes_flat_splitTorusAff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.flat_splitTorusAff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:40.239797+00:00
-- url     : https://prove2.me/theorems/662b3207-d280-40ff-b2a3-3afd6f36d9b4
-- title:
--   Semi Abelian Schemes: flat split Torus Aff
-- statement:
--   The Semi Abelian Schemes construction uses the flat split Torus Aff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SemiAbelianSchemes.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SemiAbelianSchemes.lean#L60-L66

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
variable (X : Type u) [AddCommGroup X]

theorem GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.flat_splitTorusAff : Flat (splitTorusAff ZU X).hom := by sorry
