-- Prove2me | Theorems.Thm_GlobalTheory_KerPow_locGen_theta_iff
-- name    : GlobalTheory.KerPow.locGen_theta_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:12.559044+00:00
-- url     : https://prove2.me/theorems/01571c53-e587-5b24-8174-47d4ab98bc34
-- title:
--   Ker Pow: loc Gen theta iff
-- statement:
--   The Ker Pow construction uses the loc Gen theta iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocGenOfTrivial.lean#L177-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocGenOfTrivial.lean#L177-L205

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KerPow
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem GlobalTheory.KerPow.locGen_theta_iff {L : LB A.left} (hL : L.IsLB) (hK : KTriv A L) {T : Over S}
    (sq : ∀ x y : T ⟶ A, LocGen L (K := Fin 4) (fst T A).left
      ![(translPt A (x * y)).left, (snd T A).left, (translPt A x).left, (translPt A y).left] ![1, 1, -1, -1])
    (x : T ⟶ A) (N : ℕ) :
    LocGen L (K := Fin 2) (fst T A).left ![(snd T A).left, (translPt A x).left] ![(N : ℤ), -(N : ℤ)] ↔ x ^ N = 1 := by sorry
