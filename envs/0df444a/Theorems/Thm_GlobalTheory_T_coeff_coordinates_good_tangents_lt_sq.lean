-- Prove2me | Theorems.Thm_GlobalTheory_T_coeff_coordinates_good_tangents_lt_sq
-- name    : GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:01:40.02837+00:00
-- url     : https://prove2.me/theorems/d6bbd43f-e4f2-4a6d-b634-0ad639799579
-- title:
--   T: coeff coordinates good tangents lt sq
-- statement:
--   The T construction uses the coeff coordinates good tangents lt sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffCoordinatesGoodTangentsLtSqStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffCoordinatesGoodTangentsLtSqStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSq
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSqStatement
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (em : Fin N ↪ I), (∀ δ x, S.al (em δ) 1 x = 0) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l ^ 2 → (∀ c, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (t c)) = MvPowerSeries.coeff μ (∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0)) ∧ ∀ κ : J, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (S.ze t κ)) = MvPowerSeries.coeff μ (-∑ δ : Fin N, S.be (em δ) 1 κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ V.l) := by sorry
