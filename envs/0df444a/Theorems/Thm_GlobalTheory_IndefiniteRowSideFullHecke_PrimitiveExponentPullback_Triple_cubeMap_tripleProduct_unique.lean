-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PrimitiveExponentPullback_Triple_cubeMap_tripleProduct_unique
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple.cubeMap_tripleProduct_unique
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:32.6932+00:00
-- url     : https://prove2.me/theorems/f52d0cb7-6e12-5df4-991b-6e5cb299c724
-- title:
--   Triple: cube Map triple Product unique
-- statement:
--   The Triple construction uses the cube Map triple Product unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PrimitiveExponentPullback.lean#L200-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PrimitiveExponentPullback.lean#L200-L209

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PrimitiveExponentPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [instance] Triple.grp Triple.comm
open GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple
variable {H : Host E} {S S' : Scheme.{0}}

theorem GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple.cubeMap_tripleProduct_unique {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m m' : CubeMap G' G) (h : m.F = m'.F) : m.F3 = m'.F3 := by sorry
