-- Prove2me | Theorems.Thm_GlobalTheory_AdicPt_scheme_ext
-- name    : GlobalTheory.AdicPt.scheme_ext
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:55:39.727918+00:00
-- url     : https://prove2.me/theorems/7cf8d9c2-9773-490e-903c-9e9316550aed
-- title:
--   Adic Pt: scheme ext
-- statement:
--   The Adic Pt construction uses the scheme ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniqueLim.lean#L43-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniqueLim.lean#L43-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_EqOfMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueLim
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AdicPt
open IsLocalRing
variable {R : Type} [CommRing R] [IsLocalRing R] {a : R}

theorem GlobalTheory.AdicPt.scheme_ext (ha : ¬ IsUnit a) (hc : IsAdicComplete (Ideal.span {a}) R) {Y : Scheme.{0}}
    (f g : Spec (CommRingCat.of R) ⟶ Y)
    (h : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ g) : f = g := by sorry
