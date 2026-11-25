-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeSplitCasimir_anticomm
-- name    : GlobalTheory.CompanionTheory.WedgeSplitCasimir.anticomm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:12.233628+00:00
-- url     : https://prove2.me/theorems/1c77457e-6b4b-442c-a27f-62d8ad616c35
-- title:
--   Wedge Split Casimir: anticomm
-- statement:
--   The Wedge Split Casimir construction uses the anticomm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialSignRuleQuadratic.lean#L28-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialSignRuleQuadratic.lean#L28-L73

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialSignRuleQuadratic
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeSplitCasimir

theorem GlobalTheory.CompanionTheory.WedgeSplitCasimir.anticomm {n : ℕ} (J J' : Finset (Fin n)) (s s' : Fin n) :
    (if s ∈ J' ∧ s' ∉ J'.erase s ∧ J = insert s' (J'.erase s) then
        (-1 : ℂ) ^ ((J'.erase s).filter fun c => c < s').card * (-1) ^ ((J'.erase s).filter fun c => c < s).card
      else 0) =
    (if J = J' ∧ s = s' then 1 else 0) -
      if s ∉ J ∧ s' ∉ J' ∧ insert s J = insert s' J' then
        (-1) ^ (J.filter fun a => a < s).card * (-1) ^ (J'.filter fun a => a < s').card else 0 := by sorry
