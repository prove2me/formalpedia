-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_pol_minor
-- name    : GlobalTheory.MinorNorm.pol_minor
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:28:20.520953+00:00
-- url     : https://prove2.me/theorems/7fbeff14-8ae6-4e1a-be14-d0ef49284923
-- title:
--   Minor Norm: pol minor
-- statement:
--   The Minor Norm construction uses the pol minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L335-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L335-L369

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
variable {R : Type} [CommRing R] [Algebra ℂ R] {k : ℕ} {x : Fin k → Fin k → R}
  {d : Fin k → Fin k → Derivation ℂ R R}

theorem GlobalTheory.MinorNorm.pol_minor (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0) {m : ℕ}
    (hm : m ≤ k) (i j : Fin k) (hij : i ≤ j) :
    pol x d i j (Matrix.of fun r c : Fin m => x (Fin.castLE hm r) (Fin.castLE hm c)).det =
      (if i = j ∧ (j : ℕ) < m then 1 else 0) *
        (Matrix.of fun r c : Fin m => x (Fin.castLE hm r) (Fin.castLE hm c)).det := by sorry
