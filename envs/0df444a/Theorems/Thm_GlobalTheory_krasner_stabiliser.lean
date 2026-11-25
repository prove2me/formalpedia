-- Prove2me | Theorems.Thm_GlobalTheory_krasner_stabiliser
-- name    : GlobalTheory.krasner_stabiliser
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:21:56.576805+00:00
-- url     : https://prove2.me/theorems/c6cd1590-8768-4c84-a7c7-e2a78f6f49c6
-- title:
--   Global Theory: krasner stabiliser
-- statement:
--   The Global Theory construction uses the krasner stabiliser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KrasnerLemmaDecompositionGroupStabilizerVersion.lean#L18-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KrasnerLemmaDecompositionGroupStabilizerVersion.lean#L18-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KrasnerLemmaDecompositionGroupStabilizerVersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory

theorem GlobalTheory.krasner_stabiliser (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (β β' : Ω)
    (h : ∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) :
    ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by sorry
