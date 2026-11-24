-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_pairChart_iff
-- name    : GlobalTheory.ThetaFn.exAt_mem_pairChart_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:34:31.536061+00:00
-- url     : https://prove2.me/theorems/a9f16340-61cd-44b7-a817-78644a168a3d
-- title:
--   Theta Fn: ex At mem pair Chart iff
-- statement:
--   The Theta Fn construction uses the ex At mem pair Chart iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L39-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
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

theorem GlobalTheory.ThetaFn.exAt_mem_pairChart_iff {m : T ⊗ A ⟶ A} {z w : Fin g → ℂ}
    (h : exAt u p z ≫ m.left = (u.ex w).left) (j : Fin 2 → L.ι) :
    ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j ↔
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U (j 1) := by sorry
