-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_exists_ann
-- name    : GlobalTheory.AbLaw.CubeOpen.exists_ann
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:07.856207+00:00
-- url     : https://prove2.me/theorems/2707d7f3-651d-4bae-a6d8-e0aee29dcc2a
-- title:
--   Cube Open: exists ann
-- statement:
--   The Cube Open construction uses the exists ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivBasicOpenOfTrivFibre.lean#L64-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivBasicOpenOfTrivFibre.lean#L64-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeOpen

theorem GlobalTheory.AbLaw.CubeOpen.exists_ann {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] (I : Ideal R) (hI : I.FG)
    (hIp : I ≤ p)
    (H : ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T) (e : T), (∀ r ∉ p, IsUnit (g r)) →
      (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T →
      I ≤ RingHom.ker ((Ideal.Quotient.mk (Ideal.span {e})).comp g) → I ≤ RingHom.ker g) :
    ∃ c ∉ p, ∀ x ∈ I, c * x = 0 := by sorry
