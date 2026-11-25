-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCount_casG_polar
-- name    : GlobalTheory.CompanionTheory.ZuckCount.casG_polar
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:59:07.458371+00:00
-- url     : https://prove2.me/theorems/75332310-7ea8-4a0d-8aec-3e3b20226089
-- title:
--   Zuck Count: cas G polar
-- statement:
--   The Zuck Count construction uses the cas G polar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CountingBound.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CountingBound.lean#L8-L22

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

theorem GlobalTheory.CompanionTheory.ZuckCount.casG_polar {n : ℕ} (μ : Fin n → ℝ) (J : Finset (Fin n)) (s : Fin n) :
    casG (addSet μ J) + casG (μ + Pi.single s 1) + (2 - casG μ) - casG (addSet μ J + Pi.single s 1)
      = if s ∈ J then 0 else 2 := by sorry
