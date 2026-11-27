-- Prove2me | Theorems.Thm_GlobalTheory_unimodular_of_isFundamentalDomain_finite
-- name    : GlobalTheory.unimodular_of_isFundamentalDomain_finite
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:09.226162+00:00
-- url     : https://prove2.me/theorems/18548387-fa5f-5264-90f8-9c0bfbe28755
-- title:
--   Global Theory: unimodular of is Fundamental Domain finite
-- statement:
--   The Global Theory construction uses the unimodular of is Fundamental Domain finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnimodularOfIsFundamentalDomainFinite.lean#L5-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnimodularOfIsFundamentalDomainFinite.lean#L5-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnimodularOfIsFundamentalDomainFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal ENNReal
open MeasureTheory

theorem GlobalTheory.unimodular_of_isFundamentalDomain_finite : ∀ (S : Type) [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [T2Space S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S] (Γ : Subgroup S) [Countable Γ] (μS : Measure S) (𝓢 : Set S), μS.IsHaarMeasure → IsFundamentalDomain Γ 𝓢 μS → μS 𝓢 ≠ ⊤ → μS.IsMulRightInvariant := by sorry
