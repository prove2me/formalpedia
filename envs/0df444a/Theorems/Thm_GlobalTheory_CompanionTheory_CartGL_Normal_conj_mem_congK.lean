-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_Normal_conj_mem_congK
-- name    : GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:00.031351+00:00
-- url     : https://prove2.me/theorems/9f69898c-386e-4a3a-a245-26beeb759b1c
-- title:
--   Normal: conj mem cong K
-- statement:
--   The Normal construction uses the conj mem cong K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupNormalInMaximalCompact.lean#L31-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupNormalInMaximalCompact.lean#L31-L49

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupNormalInMaximalCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.Normal
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1) (c x : GL (Fin n) L)
    (hc : c ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (hx : x ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) :
    c * x * c⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by sorry
