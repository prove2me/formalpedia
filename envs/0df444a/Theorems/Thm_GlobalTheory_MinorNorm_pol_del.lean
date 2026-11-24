-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_pol_del
-- name    : GlobalTheory.MinorNorm.pol_del
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:28:26.083949+00:00
-- url     : https://prove2.me/theorems/8ae4a4da-27bc-4575-94c9-1bdaab5b49e8
-- title:
--   Minor Norm: pol del
-- statement:
--   The Minor Norm construction uses the pol del property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L737-L777
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L737-L777

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
open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
variable {l : ℕ}
variable {σ : Type} (v : Fin l → Fin l → σ)
variable {v}

theorem GlobalTheory.MinorNorm.pol_del (hv : ∀ r c s e, v r c = v s e → r = s ∧ c = e) {k : ℕ} (hk : k ≤ l)
    (i j : Fin k) (hij : i ≤ j) (a : Fin l → ℕ) (ha : Antitone a) :
    (∀ t : Fin l, k ≤ t → a t = 0) →
      pol (fun r c => X (v (Fin.castLE hk r) (Fin.castLE hk c)))
        (fun r c => pderiv (v (Fin.castLE hk r) (Fin.castLE hk c))) i j (del v a) =
        ((if i = j then a (Fin.castLE hk j) else 0 : ℕ) : MvPolynomial σ ℂ) * del v a := by sorry
