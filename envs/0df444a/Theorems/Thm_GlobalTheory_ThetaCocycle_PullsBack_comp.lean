-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCocycle_PullsBack_comp
-- name    : GlobalTheory.ThetaCocycle.PullsBack.comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:51.86558+00:00
-- url     : https://prove2.me/theorems/7b0a7891-3f83-4fe9-a56a-8c882e427823
-- title:
--   Pulls Back: comp
-- statement:
--   The Pulls Back construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaObjectComparisonMapsCocycle.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaObjectComparisonMapsCocycle.lean#L28-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaObjectComparisonMapsCocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ThetaCocycle
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {β : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

theorem GlobalTheory.ThetaCocycle.PullsBack.comp {t'' : TObj g k J β s''} {t' : TObj g k J β s'} {t : TObj g k J β s} {f' : S'' ⟶ S'} {f : S' ⟶ S}
    {h : S'' ⟶ S} {φ' : t''.A.left ⟶ t'.A.left} {φ : t'.A.left ⟶ t.A.left} (H' : PullsBack t'' t' f' φ')
    (H : PullsBack t' t f φ) (e : f' ≫ f = h) : PullsBack t'' t h (φ' ≫ φ) := by sorry
