-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianSchemes_finitePresentation_splitTorusAff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.finitePresentation_splitTorusAff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:52.488542+00:00
-- url     : https://prove2.me/theorems/42544850-37fe-4cbc-b4d2-fc921fe5862c
-- title:
--   Semi Abelian Schemes: finite Presentation split Torus Aff
-- statement:
--   The Semi Abelian Schemes construction uses the finite Presentation split Torus Aff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SemiAbelianSchemes.lean#L68-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SemiAbelianSchemes.lean#L68-L79

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.finitePresentation_splitTorusAff [Module.Finite ℤ X] :
    LocallyOfFinitePresentation (splitTorusAff ZU X).hom := by sorry
