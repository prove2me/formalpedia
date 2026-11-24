-- Prove2me | Theorems.Thm_GlobalTheory_T_congruence_subgroup_normal_in_maximal_compact
-- name    : GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:31:54.803291+00:00
-- url     : https://prove2.me/theorems/b45cfcab-f3ea-4a47-8475-cc464655aaaf
-- title:
--   T: congruence subgroup normal in maximal compact
-- statement:
--   The T construction uses the congruence subgroup normal in maximal compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupNormalInMaximalCompactStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupNormalInMaximalCompactStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupNormalInMaximalCompact
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupNormalInMaximalCompactStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (c x : GL (Fin n) L), c ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl → x ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 → c * x * c⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by sorry
