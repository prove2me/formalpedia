-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_cmValueConst_eq
-- name    : GlobalTheory.CMVal.cmValueConst_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:36.838296+00:00
-- url     : https://prove2.me/theorems/da292375-5a2c-47ae-886f-0066206f3910
-- title:
--   CMVal: cm Value Const eq
-- statement:
--   The CMVal construction uses the cm Value Const eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L439-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L439-L441

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

theorem GlobalTheory.CMVal.cmValueConst_eq (E : Type) [Field E] [NumberField E] (d k : ℕ) (κ : I → ℕ) :
    C0 E d k κ = (|(discr (maximalRealSubfield E) : ℝ)|) ^ (((k : ℝ) - 1) / 2) * (∏ i, Real.Gamma ((k : ℝ) + κ i)) *
      (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := by sorry
