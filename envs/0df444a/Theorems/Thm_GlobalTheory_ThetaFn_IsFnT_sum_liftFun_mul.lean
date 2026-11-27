-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_IsFnT_sum_liftFun_mul
-- name    : GlobalTheory.ThetaFn.IsFnT.sum_liftFun_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:02.166993+00:00
-- url     : https://prove2.me/theorems/ee692b7a-3c14-4fc0-85ef-75fe758d6768
-- title:
--   Is Fn T: sum lift Fun mul
-- statement:
--   The Is Fn T construction uses the sum lift Fun mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L669-L675
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L669-L675

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

theorem GlobalTheory.ThetaFn.IsFnT.sum_liftFun_mul {k : ℤ} {I : Type*} (F : Finset I)
    {s : I → LB.Sec (LPow A L k (baseOver (Sp ℂ)))} {t : LB.Sec (LPow A L k (baseOver (Sp ℂ)))}
    {θ : I → (Fin g → ℂ) → ℂ} (h : ∀ i ∈ F, IsFnT u k (s i) (θ i))
    (r : I → Γ((baseOver (Sp ℂ)).left, ⊤))
    (ht : ∀ j, t.f j = ∑ i ∈ F, liftFun A _ (r i) * (s i).f j) :
    IsFnT u k t (∑ i ∈ F, numT (r i) • θ i) := by sorry
