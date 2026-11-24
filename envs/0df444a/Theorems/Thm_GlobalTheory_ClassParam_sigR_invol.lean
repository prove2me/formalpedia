-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_sigR_invol
-- name    : GlobalTheory.ClassParam.sigR_invol
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:13:39.384981+00:00
-- url     : https://prove2.me/theorems/928e04df-ea97-4a4e-8d90-b55624b48439
-- title:
--   Class Param: sig R invol
-- statement:
--   The Class Param construction uses the sig R invol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L611-L616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L611-L616

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]

theorem GlobalTheory.ClassParam.sigR_invol {L : Type} [CommRing L] [Algebra F L] (s : L →ₐ[F] L) (hs : ∀ l, s (s l) = l)
    (y : L ⊗[F] k) : sigR s k (sigR s k y) = y := by sorry
