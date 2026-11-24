-- Prove2me | Theorems.Thm_GlobalTheory_WeylInt_intQ_bidet
-- name    : GlobalTheory.WeylInt.intQ_bidet
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:56:04.632798+00:00
-- url     : https://prove2.me/theorems/66572fac-363d-460c-a7dd-566a12441be4
-- title:
--   Weyl Int: int Q bidet
-- statement:
--   The Weyl Int construction uses the int Q bidet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriIntegral.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriIntegral.lean#L32-L39

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.WeylInt
open Formalism.GradedWeylDivisibility

theorem GlobalTheory.WeylInt.intQ_bidet {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    intQ r n (bideterminant ℤ sz hsz I) = bideterminant ℚ sz hsz I := by sorry
