-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCocycle_PullsBack_cancel
-- name    : GlobalTheory.ThetaCocycle.PullsBack.cancel
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:08.084286+00:00
-- url     : https://prove2.me/theorems/e08c6396-05bb-44d4-896b-914d6b563402
-- title:
--   Pulls Back: cancel
-- statement:
--   The Pulls Back construction uses the cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaObjectComparisonMapsCocycle.lean#L39-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaObjectComparisonMapsCocycle.lean#L39-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaObjectComparisonMapsCocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_cancel

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

theorem GlobalTheory.ThetaCocycle.PullsBack.cancel {t'' : TObj g k J β s''} {t' : TObj g k J β s'} {t : TObj g k J β s} (f' : S'' ⟶ S') {f : S' ⟶ S}
    {h : S'' ⟶ S} {ψ : t''.A.left ⟶ t.A.left} {φ : t'.A.left ⟶ t.A.left} (H'' : PullsBack t'' t h ψ)
    (H : PullsBack t' t f φ) (e : f' ≫ f = h) : ∃ c, PullsBack t'' t' f' c ∧ c ≫ φ = ψ := by sorry
