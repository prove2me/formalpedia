-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_coe_glueAut
-- name    : GroundTheory.PAdicHodge.coe_glueAut
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:46:54.546279+00:00
-- url     : https://prove2.me/theorems/cb3a918d-7771-430e-91f6-fa739dbef70a
-- title:
--   PAdic Hodge: coe glue Aut
-- statement:
--   The PAdic Hodge construction uses the coe glue Aut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWGlue.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWGlue.lean#L124-L126

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FWGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {ι : Type*}
variable (Ω : IntermediateField F E) (N : ι → IntermediateField F E) (hN : ∀ i, N i ≤ Ω)
  (hdir : Directed (· ≤ ·) N) (hcov : ∀ x ∈ Ω, ∃ i, x ∈ N i) (f : ∀ i, N i →ₐ[F] N i)
  (hf : ∀ i j (h : N i ≤ N j) (x : N i), ((f j ⟨x, h x.2⟩ : N j) : E) = ((f i x : N i) : E))

theorem GroundTheory.PAdicHodge.coe_glueAut [Algebra.IsAlgebraic F Ω] (i : ι) (x : Ω) (hx : (x : E) ∈ N i) :
    ((glueAut Ω N hN hdir hcov f hf x : Ω) : E) = ((f i ⟨x, hx⟩ : N i) : E) := by sorry
