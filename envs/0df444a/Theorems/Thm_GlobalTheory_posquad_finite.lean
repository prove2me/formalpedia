-- Prove2me | Theorems.Thm_GlobalTheory_posquad_finite
-- name    : GlobalTheory.posquad_finite
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:57.076869+00:00
-- url     : https://prove2.me/theorems/b8884453-566f-415b-b632-0dc96f4a247c
-- title:
--   Global Theory: posquad finite
-- statement:
--   The Global Theory construction uses the posquad finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteSublevelOfIntQuadraticGeOne.lean#L5-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteSublevelOfIntQuadraticGeOne.lean#L5-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteSublevelOfIntQuadraticGeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.posquad_finite : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (q : X → ℤ), (∀ a, q (-a) = q a) → (∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b)) → (∀ a, a ≠ 0 → 1 ≤ q a) → ∀ N : ℤ, {a | q a ≤ N}.Finite := by sorry
