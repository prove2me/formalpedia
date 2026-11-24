-- Prove2me | Theorems.Thm_GlobalTheory_QSA_exists_nrm_one_re_sq_ne_one
-- name    : GlobalTheory.QSA.exists_nrm_one_re_sq_ne_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:03:10.447072+00:00
-- url     : https://prove2.me/theorems/98ba6a8e-efbf-4d93-bf02-47baee5e0250
-- title:
--   QSA: exists nrm one re sq ne one
-- statement:
--   The QSA construction uses the exists nrm one re sq ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsQuaternionNormOneNearReSqNeOne.lean#L10-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsQuaternionNormOneNearReSqNeOne.lean#L10-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsQuaternionNormOneNearReSqNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open Filter
open GlobalTheory GlobalTheory.QSA

theorem GlobalTheory.QSA.exists_nrm_one_re_sq_ne_one : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K], (2 : K) ≠ 0 → (𝓝[≠] (0 : K)).NeBot → ∀ a b : K, a ≠ 0 → ∀ g : ℍ[K, a, b], nrm g = 1 → ∀ W : Set ℍ[K, a, b], W ∈ 𝓝 g → ∃ g' : ℍ[K, a, b], nrm g' = 1 ∧ g'.re ^ 2 ≠ 1 ∧ W ∈ 𝓝 g' := by sorry
