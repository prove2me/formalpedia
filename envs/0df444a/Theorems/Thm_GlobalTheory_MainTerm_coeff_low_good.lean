-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_coeff_low_good
-- name    : GlobalTheory.MainTerm.coeff_low_good
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:59.233372+00:00
-- url     : https://prove2.me/theorems/3d4c603d-1b2d-4e56-9a98-7bb634b5bd6d
-- title:
--   Main Term: coeff low good
-- statement:
--   The Main Term construction uses the coeff low good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffCoordinatesGoodTangentsLtSq.lean#L51-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffCoordinatesGoodTangentsLtSq.lean#L51-L112

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSq
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
open Formalism.BaseCaseIdentities (OrdGE)
noncomputable section
open GlobalTheory GlobalTheory.MainTerm

theorem GlobalTheory.MainTerm.coeff_low_good : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (em : Fin N ↪ I), (∀ δ x, S.al (em δ) 1 x = 0) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l ^ 2 → (∀ c, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (t c)) = MvPowerSeries.coeff μ (∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0)) ∧ ∀ κ : J, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (S.ze t κ)) = MvPowerSeries.coeff μ (-∑ δ : Fin N, S.be (em δ) 1 κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ V.l) := by sorry
