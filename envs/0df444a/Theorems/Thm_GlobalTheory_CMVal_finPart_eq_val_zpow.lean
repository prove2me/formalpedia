-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_finPart_eq_val_zpow
-- name    : GlobalTheory.CMVal.finPart_eq_val_zpow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:39.801802+00:00
-- url     : https://prove2.me/theorems/2880266a-5d61-5d9e-b4de-5b5fa1dab18d
-- title:
--   CMVal: fin Part eq val zpow
-- statement:
--   The CMVal construction uses the fin Part eq val zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L173-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L173-L184

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_Formalism_L2_Host_unif_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal
open Neutral.B1 (finiteSingle)
open ReciprocityTheory.Neutral.Bridge.HCFR (infIdele)
open Formalism.L2.Host (atFin atInf unif unif_spec IsUnitAt IsUnifAt upF aboveInf)
variable (E : Type) [Field E] [NumberField E]
variable {E}
variable (E)
variable {E}
variable {I : Type} [Fintype I]

theorem GlobalTheory.CMVal.finPart_eq_val_zpow {χ : HChar E} {v : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt v) {y : (Af E)ˣ} (hy : SuppAt v y)
    {n : ℤ} (hn : Valued.v ((y : Af E) v) = WithZero.exp (-n)) : finPart χ y = χ.val v ^ n := by sorry
