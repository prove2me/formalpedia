-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_isClosedEmbedding_affPt_uncurry
-- name    : GlobalTheory.RootEx.isClosedEmbedding_affPt_uncurry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:39.537066+00:00
-- url     : https://prove2.me/theorems/faf77658-c0a3-4ea9-b01f-9587ba339df0
-- title:
--   Root Ex: is Closed Embedding aff Pt uncurry
-- statement:
--   The Root Ex construction uses the is Closed Embedding aff Pt uncurry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingAffPtUncurry.lean#L76-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingAffPtUncurry.lean#L76-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx
variable {k : Type*} [Field k] {n n' : Type*} {c : ℕ}
variable [TopologicalSpace k] [IsTopologicalRing k]

theorem GlobalTheory.RootEx.isClosedEmbedding_affPt_uncurry [T2Space k] (p : ℕ) :
    IsClosedEmbedding
      fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        affPt p z.1 z.2 := by sorry
