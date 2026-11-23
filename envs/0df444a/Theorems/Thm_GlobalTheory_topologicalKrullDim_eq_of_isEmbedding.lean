-- Prove2me | Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_isEmbedding
-- name    : GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:15.944845+00:00
-- url     : https://prove2.me/theorems/b2fa1333-61e1-4b18-8195-db0043e41991
-- title:
--   Global Theory: topological Krull Dim eq of is Embedding
-- statement:
--   The Global Theory construction uses the topological Krull Dim eq of is Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L321-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L321-L325

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open Topology TopologicalSpace

theorem GlobalTheory.topologicalKrullDim_eq_of_isEmbedding {W X : Type*} [TopologicalSpace W]
    [TopologicalSpace X] {e : W → X} (he : IsEmbedding e) {Z : Set X} (hZ : Set.range e = Z) :
    topologicalKrullDim Z = topologicalKrullDim W := by sorry
