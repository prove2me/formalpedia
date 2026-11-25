-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_natDegree_minpoly_eq_of_finrank_sup
-- name    : GroundTheory.PAdicHodge.natDegree_minpoly_eq_of_finrank_sup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:31.509647+00:00
-- url     : https://prove2.me/theorems/5ea8264b-089d-4c29-907b-5791542e5465
-- title:
--   PAdic Hodge: nat Degree minpoly eq of finrank sup
-- statement:
--   The PAdic Hodge construction uses the nat Degree minpoly eq of finrank sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L199-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L199-L241

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable {B₀ Ω : Type*} [Field B₀] [Field Ω] [Algebra B₀ Ω]

theorem GroundTheory.PAdicHodge.natDegree_minpoly_eq_of_finrank_sup {k A B : IntermediateField B₀ Ω} (hA : k ≤ A)
    (hB : k ≤ B) [FiniteDimensional B₀ A] [FiniteDimensional B₀ B]
    (h : finrank B₀ ↥(A ⊔ B) * finrank B₀ k = finrank B₀ A * finrank B₀ B) {z : Ω} (hz : z ∈ A) :
    (minpoly B z).natDegree = (minpoly k z).natDegree := by sorry
