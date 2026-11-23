-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_affPt_of_free
-- name    : GlobalTheory.RootEx.affPt_of_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:54.450318+00:00
-- url     : https://prove2.me/theorems/bfdf48f5-f3de-49dd-adc4-f0775804fa12
-- title:
--   Root Ex: aff Pt of free
-- statement:
--   The Root Ex construction uses the aff Pt of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingAffPtUncurry.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingAffPtUncurry.lean#L43-L52

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

theorem GlobalTheory.RootEx.affPt_of_free (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    affPt p x₀ e rs.1.1 rs.1.2 = basePt c (0 : Matrix n n' k) rs.1.1 rs.1.2 + e rs := by sorry
