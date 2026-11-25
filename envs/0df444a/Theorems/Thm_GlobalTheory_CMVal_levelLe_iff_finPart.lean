-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_levelLe_iff_finPart
-- name    : GlobalTheory.CMVal.levelLe_iff_finPart
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:44.868796+00:00
-- url     : https://prove2.me/theorems/a5960427-68d9-534c-b594-dccc5ee6714d
-- title:
--   CMVal: level Le iff fin Part
-- statement:
--   The CMVal construction uses the level Le iff fin Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L156-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EntireEqOfHalfPlane.lean#L156-L165

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

theorem GlobalTheory.CMVal.levelLe_iff_finPart (χ : HChar E) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    χ.LevelLe v n ↔ ∀ y : (Af E)ˣ, SuppAt v y → Valued.v ((y : Af E) v) = 1 →
      Valued.v ((y : Af E) v - 1) ≤ WithZero.exp (-(n : ℤ)) → finPart χ y = 1 := by sorry
