-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_sum_pol_det
-- name    : GlobalTheory.MinorNorm.sum_pol_det
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:28:28.642323+00:00
-- url     : https://prove2.me/theorems/cd6d3b79-8bd8-462f-8950-2ea91fbdafc1
-- title:
--   Minor Norm: sum pol det
-- statement:
--   The Minor Norm construction uses the sum pol det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L106-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L106-L136

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

theorem GlobalTheory.MinorNorm.sum_pol_det (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0) {m : ℕ}
    (ρ : Fin m → Fin k) (I : Fin (m + 1) → Fin k) (j : Fin k) :
    ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) *
        pol x d (I s) j (Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det =
      -(m * ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * (if I s = j then 1 else 0) *
        (Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det) := by sorry
