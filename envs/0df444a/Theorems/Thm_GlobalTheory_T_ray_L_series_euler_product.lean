-- Prove2me | Theorems.Thm_GlobalTheory_T_ray_L_series_euler_product
-- name    : GlobalTheory.T.ray_L_series_euler_product
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:04.35923+00:00
-- url     : https://prove2.me/theorems/c969e74a-e646-4ad4-a5dc-e9642bafb086
-- title:
--   T: ray L series euler product
-- statement:
--   The T construction uses the ray L series euler product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProductStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProductStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ray_L_series_euler_product : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → LSeriesSummable (D.coef χ) s ∧ Summable (fun v : D.Pr => ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖) ∧ LSeries (D.coef χ) s = Complex.exp (∑' v : D.Pr, -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by sorry
