-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartz_vanishing_decomposition
-- name    : GlobalTheory.T.schwartz_vanishing_decomposition
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:28.952988+00:00
-- url     : https://prove2.me/theorems/44c62dc3-9bf7-542e-ab1e-dc5ced638f14
-- title:
--   T: schwartz vanishing decomposition
-- statement:
--   The T construction uses the schwartz vanishing decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzVanishingDecompositionStatement.lean#L5-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzVanishingDecompositionStatement.lean#L5-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecompositionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartz_vanishing_decomposition : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ), f 0 = 0 → ∃ (n : ℕ) (L : Fin n → V →L[ℝ] ℝ) (h g : Fin n → SchwartzMap V ℂ),
      (∀ i x, g i x = (L i x : ℂ) * h i x) ∧ ∀ x, f x = ∑ i, g i x := by sorry
