-- Prove2me | Theorems.Thm_GlobalTheory_KerPow_locGen_pow
-- name    : GlobalTheory.KerPow.locGen_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:28:38.323019+00:00
-- url     : https://prove2.me/theorems/43d5ae83-2b91-4150-a564-08a1d853d3b6
-- title:
--   Ker Pow: loc Gen pow
-- statement:
--   The Ker Pow construction uses the loc Gen pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocGenOfTrivial.lean#L142-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocGenOfTrivial.lean#L142-L159

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

theorem GlobalTheory.KerPow.locGen_pow {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (sq : ∀ x y : T ⟶ A, LocGen L (K := Fin 4) (fst T A).left
      ![(translPt A (x * y)).left, (snd T A).left, (translPt A x).left, (translPt A y).left] ![1, 1, -1, -1])
    (x : T ⟶ A) (N : ℕ) :
    LocGen L (K := Fin 3) (fst T A).left ![(translPt A (x ^ N)).left, (snd T A).left, (translPt A x).left]
      ![-1, 1 - (N : ℤ), (N : ℤ)] := by sorry
