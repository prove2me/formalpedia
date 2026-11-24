-- Prove2me | Theorems.Thm_GlobalTheory_DoublingLength_hasSum_pairTerm_pairEquiv
-- name    : GlobalTheory.DoublingLength.hasSum_pairTerm_pairEquiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:51:50.38496+00:00
-- url     : https://prove2.me/theorems/fbf33c7e-fc71-4fcf-95a3-f2829b919274
-- title:
--   Doubling Length: has Sum pair Term pair Equiv
-- statement:
--   The Doubling Length construction uses the has Sum pair Term pair Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumSphericalFunctionDoublingLength.lean#L168-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumSphericalFunctionDoublingLength.lean#L168-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.DoublingLength
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem GlobalTheory.DoublingLength.hasSum_pairTerm_pairEquiv {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ)
    {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {len : GL (Fin n) k → ℕ}
    (hlen : ∀ e : Fin n → ℤ, Antitone e → ∀ g ∈ cell k (Fin n) ϖ e, len g = (∑ i, |e i|).toNat)
    {X : ℂ} (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) (g : GL (Fin n) k ⧸ KO k (Fin n)) :
    HasSum (fun h => pairTerm X φ (pairEquiv k n (g, h)))
      (X ^ len g.out * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) * φ g.out) := by sorry
