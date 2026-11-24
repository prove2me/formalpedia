-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_capelli_hw
-- name    : GlobalTheory.MinorNorm.capelli_hw
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:21.215378+00:00
-- url     : https://prove2.me/theorems/90e3efb4-ecd3-493d-b99d-c6fc21bb6257
-- title:
--   Minor Norm: capelli hw
-- statement:
--   The Minor Norm construction uses the capelli hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L311-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L311-L326

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {k : ℕ} (x : Fin k → Fin k → R) (d : Fin k → Fin k → Derivation ℂ R R)
variable {x d}

theorem GlobalTheory.MinorNorm.capelli_hw (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0)
    (a : Fin k → ℕ) (P : R) (hup : ∀ i j, i < j → pol x d i j P = 0)
    (hwt : ∀ j, pol x d j j P = a j * P) :
    (Matrix.of x).det * ∑ ρ : Fin k → Fin k, (eps ρ : R) * iterD d k ρ id P =
      ((∏ t, (a t + (k - (t + 1))) : ℕ) : R) * P := by sorry
