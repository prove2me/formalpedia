-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_isFnAt_iff_of_isPullSec
-- name    : GlobalTheory.ThetaFn.isFnAt_iff_of_isPullSec
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:42:37.926943+00:00
-- url     : https://prove2.me/theorems/7e0b529b-e720-42f6-963d-6557b11058d1
-- title:
--   Theta Fn: is Fn At iff of is Pull Sec
-- statement:
--   The Theta Fn construction uses the is Fn At iff of is Pull Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L572-L581
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L572-L581

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
variable (u p)
variable {u p}

theorem GlobalTheory.ThetaFn.isFnAt_iff_of_isPullSec {T' : Over (Sp ℂ)} {p' : 𝟙_ (Over (Sp ℂ)) ⟶ T'}
    {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A} {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {s' : LB.Sec (LPow A L k T')} (hs : IsPullSec A L k h hh s s')
    (hp : ∀ z, exAt u p' z ≫ h.left = exAt u p z) (θ : (Fin g → ℂ) → ℂ) :
    IsFnAt u p' k s' θ ↔ IsFnAt u p k s θ := by sorry
