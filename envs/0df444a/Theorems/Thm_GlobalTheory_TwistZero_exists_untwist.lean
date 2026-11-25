-- Prove2me | Theorems.Thm_GlobalTheory_TwistZero_exists_untwist
-- name    : GlobalTheory.TwistZero.exists_untwist
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:13:36.732615+00:00
-- url     : https://prove2.me/theorems/8a2284a7-0b07-4194-a008-bf357208aba8
-- title:
--   Twist Zero: exists untwist
-- statement:
--   The Twist Zero construction uses the exists untwist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/TorsionZeroCountTwist.lean#L144-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/TorsionZeroCountTwist.lean#L144-L166

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_TorsionZeroCountTwist
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistZero

theorem GlobalTheory.TwistZero.exists_untwist {k : Type} [Field k] (hsq : SquareSt) (P : PolAV (Sp k)) (q : ℕ) (hq : 2 ≤ q)
    (b : baseOver (Sp k) ⟶ P.A) (s : LB.Sec (twistLB P.A P.L q (b ^ q))) :
    ∃ s' : (lbPow P.L q).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseOver (Sp k) ⊗ P.A).left) (z : Z)
      (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J → ∃ u : (Z.presheaf.stalk z)ˣ,
        sval s' (r ≫ (translPt P.A b).left) z J =
          sval (φ := ![(snd (baseOver (Sp k)) P.A).left, (translPt P.A (b ^ q)).left])
            (ε := ![(q : ℤ) - 1, 1]) s r z J * u := by sorry
