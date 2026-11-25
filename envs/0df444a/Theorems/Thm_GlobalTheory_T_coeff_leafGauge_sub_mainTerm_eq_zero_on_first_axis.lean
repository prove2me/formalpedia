-- Prove2me | Theorems.Thm_GlobalTheory_T_coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis
-- name    : GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:40:37.421214+00:00
-- url     : https://prove2.me/theorems/7fb9e938-d19d-4bd0-bb89-1ecc7423e90c
-- title:
--   T: coeff leaf Gauge sub main Term eq zero on first axis
-- statement:
--   The T construction uses the coeff leaf Gauge sub main Term eq zero on first axis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffLeafGaugeSubMainTermEqZeroOnFirstAxisStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffLeafGaugeSubMainTermEqZeroOnFirstAxisStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxisStatement
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

theorem GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (i : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C) (Φ : ι' → ι → C) (μ : ι ⊕ ι' →₀ ℕ), (∀ b, μ (Sum.inr b) = 0) → MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0 := by sorry
