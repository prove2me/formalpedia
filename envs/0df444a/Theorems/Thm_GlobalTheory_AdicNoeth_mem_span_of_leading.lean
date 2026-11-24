-- Prove2me | Theorems.Thm_GlobalTheory_AdicNoeth_mem_span_of_leading
-- name    : GlobalTheory.AdicNoeth.mem_span_of_leading
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:54:44.414852+00:00
-- url     : https://prove2.me/theorems/e2f239dc-4272-46d9-b9d3-4cfae3b24094
-- title:
--   Adic Noeth: mem span of leading
-- statement:
--   The Adic Noeth construction uses the mem span of leading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsNoetherianRingOfIsAdicComplete.lean#L82-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsNoetherianRingOfIsAdicComplete.lean#L82-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsNoetherianRingOfIsAdicComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.AdicNoeth

theorem GlobalTheory.AdicNoeth.mem_span_of_leading {R : Type} [CommRing R] (I : Ideal R) [hc : IsAdicComplete I R]
    (J : Ideal R) {ι : Type} [Fintype ι] (f : ι → R) (d : ι → ℕ) (hf : ∀ i, f i ∈ J)
    (h : ∀ (n : ℕ) (g : R), g ∈ J → g ∈ I ^ n →
        ∃ c : ι → R, (∀ i, c i ∈ I ^ (n - d i)) ∧ g - ∑ i, c i * f i ∈ I ^ (n + 1))
    (g : R) (hg : g ∈ J) : g ∈ Ideal.span (Set.range f) := by sorry
