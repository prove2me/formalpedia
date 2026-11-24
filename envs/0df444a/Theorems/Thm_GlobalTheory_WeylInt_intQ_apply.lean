-- Prove2me | Theorems.Thm_GlobalTheory_WeylInt_intQ_apply
-- name    : GlobalTheory.WeylInt.intQ_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:02.184485+00:00
-- url     : https://prove2.me/theorems/c500688f-83bb-4ff8-92f2-af26ae69ea23
-- title:
--   Weyl Int: int Q apply
-- statement:
--   The Weyl Int construction uses the int Q apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriIntegral.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriIntegral.lean#L29-L30

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

theorem GlobalTheory.WeylInt.intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = MvPolynomial.map (Int.castRingHom ℚ) P := by sorry
