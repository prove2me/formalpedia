-- Prove2me | Theorems.Thm_GlobalTheory_MulUnramified_eq_one_of_pow_eq_one
-- name    : GlobalTheory.MulUnramified.eq_one_of_pow_eq_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:28:33.108781+00:00
-- url     : https://prove2.me/theorems/5413a3be-0ec4-4daa-956f-9659b370b376
-- title:
--   Mul Unramified: eq one of pow eq one
-- statement:
--   The Mul Unramified construction uses the eq one of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L95-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FormallyUnramifiedMulN.lean#L95-L174

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

theorem GlobalTheory.MulUnramified.eq_one_of_pow_eq_one (G : Over S) [GrpObj G] {T₀ T : Over S} (j : T₀ ⟶ T)
    (hj : Function.Surjective j.left)
    (hsq : ∀ (W : T.left.Opens), IsAffineOpen W → ∀ s t : Γ(T.left, W),
      j.left.app W s = 0 → j.left.app W t = 0 → s * t = 0)
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (z : T ⟶ G) (hz : j ≫ z = 1) (hzn : z ^ n = 1) :
    z = 1 := by sorry
