-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_exAt_translPt
-- name    : GlobalTheory.ThetaFn.exAt_translPt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:38:25.994793+00:00
-- url     : https://prove2.me/theorems/d9e733b3-5507-4596-9121-a90a06181ff7
-- title:
--   Theta Fn: ex At transl Pt
-- statement:
--   The Theta Fn construction uses the ex At transl Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasAnConstThetaGrpZeroIff.lean#L264-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasAnConstThetaGrpZeroIff.lean#L264-L270

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
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
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {p}

theorem GlobalTheory.ThetaFn.exAt_translPt {y : T ⟶ A} {x : Fin g → ℂ} (hy : p ≫ y = u.ex x) (z : Fin g → ℂ) :
    exAt u p z ≫ (translPt A y).left = (u.ex (z + x)).left := by sorry
