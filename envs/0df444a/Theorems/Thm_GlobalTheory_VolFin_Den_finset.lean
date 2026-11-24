-- Prove2me | Theorems.Thm_GlobalTheory_VolFin_Den_finset
-- name    : GlobalTheory.VolFin.Den.finset
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:50:36.102009+00:00
-- url     : https://prove2.me/theorems/026fd582-40d1-47d1-a350-bb5204047b30
-- title:
--   Den: finset
-- statement:
--   The Den construction uses the finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L30-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.VolFin
open Module Filter Topology
variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}

theorem GlobalTheory.VolFin.Den.finset {R : ι → Subalgebra K F} {γ : ι → F} (h : Den R γ) (s : Finset F) :
    ∃ c, ∃ q ∈ piece R γ c, q ≠ 0 ∧ ∀ u ∈ s, q * u ∈ piece R γ c := by sorry
