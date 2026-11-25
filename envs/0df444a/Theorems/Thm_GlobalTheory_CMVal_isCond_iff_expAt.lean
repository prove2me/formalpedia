-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_isCond_iff_expAt
-- name    : GlobalTheory.CMVal.isCond_iff_expAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:41.113214+00:00
-- url     : https://prove2.me/theorems/5524532c-8643-4a86-8d68-bd872c2cf0e0
-- title:
--   CMVal: is Cond iff exp At
-- statement:
--   The CMVal construction uses the is Cond iff exp At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L266-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L266-L277

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

theorem GlobalTheory.CMVal.isCond_iff_expAt (χ : HChar E) {𝔣 : Ideal (𝓞 E)} (h𝔣 : 𝔣 ≠ ⊥) :
    χ.IsCond 𝔣 ↔ ∀ v, ExpAt χ v (multiplicity v.asIdeal 𝔣) := by sorry
