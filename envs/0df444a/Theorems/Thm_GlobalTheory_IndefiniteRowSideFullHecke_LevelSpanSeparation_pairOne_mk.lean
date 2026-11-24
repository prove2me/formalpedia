-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LevelSpanSeparation_pairOne_mk
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.pairOne_mk
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:06.970414+00:00
-- url     : https://prove2.me/theorems/aa2dbd35-5e52-498a-864f-0408f3d2452c
-- title:
--   Level Span Separation: pair One mk
-- statement:
--   The Level Span Separation construction uses the pair One mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/LevelIndexFourierCharacter.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/LevelIndexFourierCharacter.lean#L111-L117

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable (D : Datum H) (l : Level H)

theorem GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.pairOne_mk {c : 𝓞 E} (hc : IsSep l c) (u v : D.La) :
    pairOne D l (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = ((D.EF u (c • v) : ℤ) : ZMod l.M) := by sorry
