-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisConv_exists_short_generators
-- name    : GlobalTheory.SW.EisConv.exists_short_generators
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:49.250625+00:00
-- url     : https://prove2.me/theorems/e503045b-f444-4f6c-bbe6-1477101085a2
-- title:
--   Eis Conv: exists short generators
-- statement:
--   The Eis Conv construction uses the exists short generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L131-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L131-L170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem GlobalTheory.SW.EisConv.exists_short_generators {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (N c : ℕ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ γ ∈ UU E N, Den c γ → ∃ w : Fin N → (Fin N ⊕ Fin N → 𝓞 E),
      Submodule.span E (Set.range fun i j => (w i j : E)) = botSpan γ ∧ (∀ i, w i ≠ 0) ∧
      ∏ i, ‖embAll E _ (w i)‖ ^ Ψ.card ≤
        K * ∏ τ : Ψ, ‖(hDen Ψ γ (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det‖ := by sorry
