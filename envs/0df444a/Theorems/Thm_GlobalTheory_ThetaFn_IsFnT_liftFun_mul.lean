-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_IsFnT_liftFun_mul
-- name    : GlobalTheory.ThetaFn.IsFnT.liftFun_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:33.061797+00:00
-- url     : https://prove2.me/theorems/36d986f3-a15e-5657-9aab-0de42875f27d
-- title:
--   Is Fn T: lift Fun mul
-- statement:
--   The Is Fn T construction uses the lift Fun mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L664-L667
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L664-L667

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
variable {u}

theorem GlobalTheory.ThetaFn.IsFnT.liftFun_mul {k : ℤ} {s t : LB.Sec (LPow A L k (baseOver (Sp ℂ)))}
    {θ : (Fin g → ℂ) → ℂ} (h : IsFnT u k s θ) (r : Γ((baseOver (Sp ℂ)).left, ⊤))
    (ht : ∀ j, t.f j = liftFun A _ r * s.f j) : IsFnT u k t (numT r • θ) := by sorry
