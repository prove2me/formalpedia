-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisBdd_pair
-- name    : GlobalTheory.SW.EisBdd.pair
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:48:28.612084+00:00
-- url     : https://prove2.me/theorems/b08f2624-bd4c-48f1-b6f7-c3c540e29765
-- title:
--   Eis Bdd: pair
-- statement:
--   The Eis Bdd construction uses the pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianThetaEisensteinConvergeBounded.lean#L180-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianThetaEisensteinConvergeBounded.lean#L180-L199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBounded
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisBdd
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

theorem GlobalTheory.SW.EisBdd.pair {γ : M2 E N} (h : γ ∈ UU E N) (τ : Ψ) :
    (γ.toBlocks₂₁.map τ.1 * (γ.toBlocks₂₂.map τ.1)ᴴ).IsHermitian ∧
    (γ.toBlocks₂₁.map τ.1 * (γ.toBlocks₂₁.map τ.1)ᴴ +
      γ.toBlocks₂₂.map τ.1 * (γ.toBlocks₂₂.map τ.1)ᴴ).PosDef ∧
    (hDen Ψ γ (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det ≠ 0 := by sorry
