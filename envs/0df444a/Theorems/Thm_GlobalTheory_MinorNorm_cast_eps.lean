-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_cast_eps
-- name    : GlobalTheory.MinorNorm.cast_eps
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:28:13.198565+00:00
-- url     : https://prove2.me/theorems/4e8ae95d-1274-49e5-9945-3fc8f831ea1d
-- title:
--   Minor Norm: cast eps
-- statement:
--   The Minor Norm construction uses the cast eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L292-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L292-L298

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

theorem GlobalTheory.MinorNorm.cast_eps (ρ : Fin k → Fin k) :
    ((eps ρ : ℤ) : R) = (Matrix.of fun t s => if ρ t = s then (1 : R) else 0).det := by sorry
