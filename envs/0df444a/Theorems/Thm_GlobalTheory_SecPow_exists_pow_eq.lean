-- Prove2me | Theorems.Thm_GlobalTheory_SecPow_exists_pow_eq
-- name    : GlobalTheory.SecPow.exists_pow_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:55:39.392138+00:00
-- url     : https://prove2.me/theorems/6277e80b-e222-5314-9248-91397c054447
-- title:
--   Sec Pow: exists pow eq
-- statement:
--   The Sec Pow construction uses the exists pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPowSection.lean#L66-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPowSection.lean#L66-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.SecPow
variable {X X' : Scheme.{0}}

theorem GlobalTheory.SecPow.exists_pow_eq {W O : X.Opens} (hW : IsCompact (W : Set X)) (hO : O ≤ W) (x y : Γ(X, W))
    (hsq : (y - x) * (y - x) = 0) (hx : X.basicOpen x ≤ O) (h : rs X hO x = rs X hO y) :
    ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → x ^ l = y ^ l := by sorry
