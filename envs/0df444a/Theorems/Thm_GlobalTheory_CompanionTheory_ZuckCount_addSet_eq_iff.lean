-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCount_addSet_eq_iff
-- name    : GlobalTheory.CompanionTheory.ZuckCount.addSet_eq_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:55:58.6061+00:00
-- url     : https://prove2.me/theorems/c0c1f0de-10a3-40df-9800-a12f86bfc154
-- title:
--   Zuck Count: add Set eq iff
-- statement:
--   The Zuck Count construction uses the add Set eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CountingBound.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CountingBound.lean#L32-L48

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CountingBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckCount

theorem GlobalTheory.CompanionTheory.ZuckCount.addSet_eq_iff {n : ℕ} (μ : Fin n → ℝ) (J I : Finset (Fin n)) (s : Fin n) :
    addSet μ J + Pi.single s 1 = addSet μ I ↔ s ∉ J ∧ I = insert s J := by sorry
