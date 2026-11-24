-- Prove2me | Theorems.Thm_GlobalTheory_Serre_iSupIndep_eigen
-- name    : GlobalTheory.Serre.iSupIndep_eigen
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:23.210664+00:00
-- url     : https://prove2.me/theorems/8a0c5874-ec58-43b8-9120-a87baa7fc881
-- title:
--   Serre: i Sup Indep eigen
-- statement:
--   The Serre construction uses the i Sup Indep eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L246-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedRingOfIntegers.lean#L246-L251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.Serre

theorem GlobalTheory.Serre.iSupIndep_eigen {k V I : Type*} [Field k] [AddCommGroup V] [Module k V]
    (f : I → Module.End k V) (hf : ∀ i j, Commute (f i) (f j)) :
    iSupIndep fun χ : I → k ↦ ⨅ i, (f i).eigenspace (χ i) := by sorry
