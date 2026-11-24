-- Prove2me | Theorems.Thm_GlobalTheory_JointHarm_coeff_rename_mul
-- name    : GlobalTheory.JointHarm.coeff_rename_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:40.857235+00:00
-- url     : https://prove2.me/theorems/affdc217-6841-4dfb-bc9f-a3cdfbe4ea3e
-- title:
--   Joint Harm: coeff rename mul
-- statement:
--   The Joint Harm construction uses the coeff rename mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JointHarmonicOfHookNorm.lean#L66-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JointHarmonicOfHookNorm.lean#L66-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LowerUnipotentMinors
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JointHarmonicOfHookNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JointHarm
open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials
variable {n p q : ℕ}
open Formalism.E
variable {σ₁ σ₂ τ : Type} {f : σ₁ → τ} {g : σ₂ → τ}

theorem GlobalTheory.JointHarm.coeff_rename_mul (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (α : σ₁ →₀ ℕ) (β : σ₂ →₀ ℕ) (P : MvPolynomial σ₁ ℂ)
    (Q : MvPolynomial σ₂ ℂ) :
    coeff (α.mapDomain f + β.mapDomain g) (rename f P * rename g Q) = coeff α P * coeff β Q := by sorry
