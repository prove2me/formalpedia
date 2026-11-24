-- Prove2me | Theorems.Thm_GlobalTheory_DoublingLength_pairTerm_pairEquiv
-- name    : GlobalTheory.DoublingLength.pairTerm_pairEquiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:52:23.520102+00:00
-- url     : https://prove2.me/theorems/dbdd4779-a692-4aea-990f-e43ffc8117ce
-- title:
--   Doubling Length: pair Term pair Equiv
-- statement:
--   The Doubling Length construction uses the pair Term pair Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumSphericalFunctionDoublingLength.lean#L144-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumSphericalFunctionDoublingLength.lean#L144-L166

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
open scoped Classical

theorem GlobalTheory.DoublingLength.pairTerm_pairEquiv {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (X : ℂ)
    (g h : GL (Fin n) k ⧸ KO k (Fin n)) :
    pairTerm X φ (pairEquiv k n (g, h)) =
      if (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
          (∀ i j, (h.out⁻¹ * g.out : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
        X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat +
          (ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out))).toNat) * φ g.out
      else 0 := by sorry
