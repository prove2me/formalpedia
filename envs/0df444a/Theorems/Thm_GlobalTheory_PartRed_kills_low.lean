-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_kills_low
-- name    : GlobalTheory.PartRed.kills_low
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:15.701656+00:00
-- url     : https://prove2.me/theorems/d77fb1e3-2fd1-4ff4-966c-f954b38961e0
-- title:
--   Part Red: kills low
-- statement:
--   The Part Red construction uses the kills low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapLawsFactorFourierJacobiSource.lean#L234-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapLawsFactorFourierJacobiSource.lean#L234-L266

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMulAddCharLinearFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqFlatMapFourierJacobiRowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiRowAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapLawsFactorFourierJacobiSource
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.PartRed
open GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
  {M : Type} [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.PartRed.kills_low (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hν : ν.IsAddHaarMeasure) (ρ : ℕ) (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hc : c = 2 * ρ + 1)
    (H4 : ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ)
    (K : Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ) (transSet ρ)) :
    ∀ j : ℕ, Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ (lowSet ρ).filter (fun e => colIx e < j))
      (transSet ρ) := by sorry
