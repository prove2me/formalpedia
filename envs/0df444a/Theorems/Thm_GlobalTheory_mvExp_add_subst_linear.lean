-- Prove2me | Theorems.Thm_GlobalTheory_mvExp_add_subst_linear
-- name    : GlobalTheory.mvExp_add_subst_linear
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:28.484866+00:00
-- url     : https://prove2.me/theorems/46fa4742-813e-4a1e-b6ad-d069136f742a
-- title:
--   Global Theory: mv Exp add subst linear
-- statement:
--   The Global Theory construction uses the mv Exp add subst linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MfactMulCoeffMvExpLinear.lean#L64-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MfactMulCoeffMvExpLinear.lean#L64-L81

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MfactMulCoeffMvExpLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open GlobalTheory

theorem GlobalTheory.mvExp_add_subst_linear : ∀ (C : Type) [Field C] [CharZero C] (σ : Type) [Fintype σ],
  (∀ a b : MvPowerSeries σ C, MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 → mvExp (a + b) = mvExp a * mvExp b) ∧
  (∀ a : MvPowerSeries σ C, MvPowerSeries.constantCoeff a = 0 → mvExp a = PowerSeries.subst a (PowerSeries.exp C)) ∧
  (∀ (τ : Type) [Fintype τ] (φ : σ → MvPowerSeries τ C) (a : MvPowerSeries σ C), (∀ s, MvPowerSeries.constantCoeff (φ s) = 0) → MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.subst φ (mvExp a) = mvExp (MvPowerSeries.subst φ a)) ∧
  (∀ (y : σ → C) (P : MvPolynomial σ C), jetAt0 P (mvExp (∑ s, y s • (MvPowerSeries.X s : MvPowerSeries σ C))) = MvPolynomial.eval y P) := by sorry
