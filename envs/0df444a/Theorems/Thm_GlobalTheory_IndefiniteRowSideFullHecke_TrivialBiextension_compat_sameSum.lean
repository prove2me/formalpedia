-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_compat_sameSum
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension.compat_sameSum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:28.17286+00:00
-- url     : https://prove2.me/theorems/58c2f7c0-5eb2-477f-95bf-bef5569ed4d9
-- title:
--   Trivial Biextension: compat same Sum
-- statement:
--   The Trivial Biextension construction uses the compat same Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/TrivialBiextension.lean#L136-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/TrivialBiextension.lean#L136-L150

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_TrivialBiextension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

theorem GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension.compat_sameSum {T : Over S} (a a' b b' : T ⟶ G) :
    LB.SameSum
      (Sum.elim (law₂φ G (padd G a a') b b') (Sum.elim (law₁φ G a a' b) (law₁φ G a a' b')))
      (Sum.elim lawε (Sum.elim lawε lawε))
      (Sum.elim (law₁φ G a a' (padd G b b')) (Sum.elim (law₂φ G a b b') (law₂φ G a' b b')))
      (Sum.elim lawε (Sum.elim lawε lawε)) := by sorry
