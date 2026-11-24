-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeatTerm_hFac_inv_at
-- name    : GlobalTheory.SW.HeatTerm.hFac_inv_at
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:40:44.09338+00:00
-- url     : https://prove2.me/theorems/539bd7ff-4b8e-4b5d-98d7-cbb1cdf56f3e
-- title:
--   Heat Term: h Fac inv at
-- statement:
--   The Heat Term construction uses the h Fac inv at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L189-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L189-L200

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open Classical
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.HeatTerm.hFac_inv_at (γ : M2 E N) (Z : CM Ψ N N) (z z' : CM Ψ n N) (τ : Ψ)
    (W : Matrix (Fin N) (Fin N) ℂ) (w w' : Matrix (Fin n) (Fin N) ℂ) :
    (hFac Ψ γ (fun σ => Z σ + if σ = τ then W else 0) (fun σ => z σ + if σ = τ then w else 0)
      (fun σ => z' σ + if σ = τ then w' else 0))⁻¹ =
    (∏ σ ∈ Finset.univ.erase τ,
      loc (γ.toBlocks₂₁.map σ.1) (γ.toBlocks₂₂.map σ.1) (Z σ) (z σ) (z' σ)) *
      loc (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) (Z τ + W) (z τ + w) (z' τ + w') := by sorry
