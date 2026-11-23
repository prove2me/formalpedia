-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_beta_eq
-- name    : GlobalTheory.CMVal.beta_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:07.558011+00:00
-- url     : https://prove2.me/theorems/0839ec3d-f41f-473a-b19e-32aeb22b66af
-- title:
--   CMVal: beta eq
-- statement:
--   The CMVal construction uses the beta eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L456-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L456-L457

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

theorem GlobalTheory.CMVal.beta_eq (E : Type) [Field E] [NumberField E] (d s : ℕ) (κ : I → ℕ) (Λ : PeriodPair) (T : ℂ) :
    beta E d s κ Λ T = ((C0 E d (2 * s) κ : ℂ) * T) ^ 12 / latDisc Λ ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i) := by sorry
