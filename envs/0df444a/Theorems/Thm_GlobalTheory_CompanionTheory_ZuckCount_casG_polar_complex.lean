-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCount_casG_polar_complex
-- name    : GlobalTheory.CompanionTheory.ZuckCount.casG_polar_complex
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:59:23.763406+00:00
-- url     : https://prove2.me/theorems/277dc39b-24d8-5fc6-8d29-063e416cf40a
-- title:
--   Zuck Count: cas G polar complex
-- statement:
--   The Zuck Count construction uses the cas G polar complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CountingBound.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CountingBound.lean#L50-L54

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

theorem GlobalTheory.CompanionTheory.ZuckCount.casG_polar_complex {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) :
    (casG (addSet μ J) : ℂ) + (casG (μ + Pi.single s 1) : ℂ) + (2 - (casG μ : ℂ))
      - (casG (addSet μ J + Pi.single s 1) : ℂ) = if s ∈ J then 0 else 2 := by sorry
