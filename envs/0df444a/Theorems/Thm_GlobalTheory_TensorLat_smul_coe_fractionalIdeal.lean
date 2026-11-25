-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_smul_coe_fractionalIdeal
-- name    : GlobalTheory.TensorLat.smul_coe_fractionalIdeal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:03:39.959053+00:00
-- url     : https://prove2.me/theorems/d789eb3f-5097-4009-a3cf-dd44a7f90767
-- title:
--   Tensor Lat: smul coe fractional Ideal
-- statement:
--   The Tensor Lat construction uses the smul coe fractional Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoeEqSpanDetOfIntVecLe.lean#L224-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoeEqSpanDetOfIntVecLe.lean#L224-L234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors
open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx ReciprocityTheory.PGsh
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem GlobalTheory.TensorLat.smul_coe_fractionalIdeal (𝔫 : Ideal (𝓞 K)) (J : FractionalIdeal (𝓞 K)⁰ K) :
    𝔫 • (J : Submodule (𝓞 K) K) =
      (((𝔫 : FractionalIdeal (𝓞 K)⁰ K) * J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by sorry
