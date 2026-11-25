-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PrimitiveExponentPullback_Triple_PullIso_toPull_surjective
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple.PullIso.toPull_surjective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:03.345558+00:00
-- url     : https://prove2.me/theorems/5e595539-03e2-4566-b395-dfbe6838d5f6
-- title:
--   Pull Iso: to Pull surjective
-- statement:
--   The Pull Iso construction uses the to Pull surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PrimitiveExponentPullback.lean#L184-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PrimitiveExponentPullback.lean#L184-L187

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple.PullIso.toPull_surjective {t' : Triple H S'} {t : Triple H S} {f : S' ⟶ S} :
    Function.Surjective (PullIso.toPull (t' := t') (t := t) (f := f)) := by sorry
