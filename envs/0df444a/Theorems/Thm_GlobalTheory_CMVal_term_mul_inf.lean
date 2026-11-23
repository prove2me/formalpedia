-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_term_mul_inf
-- name    : GlobalTheory.CMVal.term_mul_inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:39.548514+00:00
-- url     : https://prove2.me/theorems/0fa24df3-35af-47fd-86ba-65611758c99f
-- title:
--   CMVal: term mul inf
-- statement:
--   The CMVal construction uses the term mul inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L417-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L417-L429

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

theorem GlobalTheory.CMVal.term_mul_inf {χ : HChar E} {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    (h : HasInfRatio χ φ fun i => (κ i : ℤ) + s) (a : Eˣ) :
    term φ (2 * s) κ 0 a * (((χ.inf a : ℂˣ) : ℂ) * ∏ i, (φ i a * starRingEnd ℂ (φ i a)) ^ s) = 1 := by sorry
