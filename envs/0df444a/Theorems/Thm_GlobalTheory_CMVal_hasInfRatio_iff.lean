-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_hasInfRatio_iff
-- name    : GlobalTheory.CMVal.hasInfRatio_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:11.775921+00:00
-- url     : https://prove2.me/theorems/cb026e99-8a0e-48c2-a2a6-5c1e60f3d872
-- title:
--   CMVal: has Inf Ratio iff
-- statement:
--   The CMVal construction uses the has Inf Ratio iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L225-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L225-L235

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

theorem GlobalTheory.CMVal.hasInfRatio_iff (χ : HChar E) (φ : I → E →+* ℂ) (m : I → ℤ) :
    HasInfRatio χ φ m ↔
      ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i (k : E) / starRingEnd ℂ (φ i (k : E))) ^ m i := by sorry
