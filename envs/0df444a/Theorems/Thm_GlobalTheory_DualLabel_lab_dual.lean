-- Prove2me | Theorems.Thm_GlobalTheory_DualLabel_lab_dual
-- name    : GlobalTheory.DualLabel.lab_dual
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:01:41.379793+00:00
-- url     : https://prove2.me/theorems/05e94385-3118-4fd9-b854-f767ed9dc791
-- title:
--   Dual Label: lab dual
-- statement:
--   The Dual Label construction uses the lab dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RootsReverseProd.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RootsReverseProd.lean#L54-L65

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.DualLabel

theorem GlobalTheory.DualLabel.lab_dual : ∀ {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O →
    ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Simple τ' →
    Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ' →
    (∀ γ : GL (Fin d) K, LinearMap.trace ℂ τ'.V (τ'.ρ γ) = LinearMap.trace ℂ τ.V (τ.ρ γ⁻¹)) →
    O.lab d τ' = Polynomial.C ((O.lab d τ).coeff 0)⁻¹ * (O.lab d τ).reverse := by sorry
