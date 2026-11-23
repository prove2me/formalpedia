-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_exists_iInf_sub_mem
-- name    : GlobalTheory.CoeffSubring.exists_iInf_sub_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:07.684973+00:00
-- url     : https://prove2.me/theorems/d84322f1-3d73-428b-8a8a-7f999a9e580f
-- title:
--   Coeff Subring: exists i Inf sub mem
-- statement:
--   The Coeff Subring construction uses the exists i Inf sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L105-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L105-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
variable {p L}

theorem GlobalTheory.CoeffSubring.exists_iInf_sub_mem [IsAdicComplete (maximalIdeal S) S] (h0 : (p : S) ∈ maximalIdeal S)
    (hs : ∀ n s, ∃ t ∈ level p L n, s - t ∈ maximalIdeal S) (s : S) :
    ∃ a ∈ ⨅ n, level p L n, s - a ∈ maximalIdeal S := by sorry
