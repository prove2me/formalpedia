-- Prove2me | Theorems.Thm_GlobalTheory_MulUnramified_mul_eq_zero_of_ker_sq
-- name    : GlobalTheory.MulUnramified.mul_eq_zero_of_ker_sq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:27:38.064661+00:00
-- url     : https://prove2.me/theorems/181aa714-2fee-47f8-b853-e112dae4b1af
-- title:
--   Mul Unramified: mul eq zero of ker sq
-- statement:
--   The Mul Unramified construction uses the mul eq zero of ker sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L176-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L176-L199

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulUnramified
variable {S : Scheme.{0}}

theorem GlobalTheory.MulUnramified.mul_eq_zero_of_ker_sq {R R₀ : CommRingCat.{0}} (φ : R ⟶ R₀) (hφ : RingHom.ker φ.hom ^ 2 = ⊥)
    (W : (Spec R).Opens) (hW : IsAffineOpen W) (s t : Γ(Spec R, W))
    (hs : (Spec.map φ).app W s = 0) (ht : (Spec.map φ).app W t = 0) : s * t = 0 := by sorry
