-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianSchemes_isTorusExtension_splitTorus
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.isTorusExtension_splitTorus
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:50.612179+00:00
-- url     : https://prove2.me/theorems/36d5abd0-2512-4f5d-bc74-909814013dd3
-- title:
--   Semi Abelian Schemes: is Torus Extension split Torus
-- statement:
--   The Semi Abelian Schemes construction uses the is Torus Extension split Torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SemiAbelianSchemes.lean#L81-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SemiAbelianSchemes.lean#L81-L100

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.isTorusExtension_splitTorus (k : Type u) [Field k] [Module.Free ℤ X] [Module.Finite ℤ X] :
    IsTorusExtension (splitTorus (Spec (CommRingCat.of k)) X) := by sorry
