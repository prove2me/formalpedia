-- Prove2me | Theorems.Thm_GlobalTheory_SW_Reduct_exists_rows
-- name    : GlobalTheory.SW.Reduct.exists_rows
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:08:14.215413+00:00
-- url     : https://prove2.me/theorems/383c0a62-a0d2-49d3-a7d6-59054bba0a77
-- title:
--   Reduct: exists rows
-- statement:
--   The Reduct construction uses the exists rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryMoveHermitianHalfSpaceHigh.lean#L171-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsUnitaryMoveHermitianHalfSpaceHigh.lean#L171-L281

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHigh
import Theorems.Thm_GlobalTheory_SW_NearPrim_exists_rows

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Reduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.Reduct.exists_rows {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Z ∈ Hn Ψ N, ∃ W : Matrix (Fin N) (Fin N ⊕ Fin N) E, IntM W ∧
      LinearIndependent E (fun i => W i) ∧ W * Matrix.J (Fin N) E * ccT W = 0 ∧
      ∀ τ : Ψ, (W.map τ.1 * (fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ) * (imH (Z τ))⁻¹ *
        (fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ) * (W.map τ.1)ᴴ).trace.re ≤ B := by sorry
