-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_coe_glueHom
-- name    : GroundTheory.PAdicHodge.coe_glueHom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:46:35.750691+00:00
-- url     : https://prove2.me/theorems/82fb1316-0854-44ac-b0a0-2ebb05c07687
-- title:
--   PAdic Hodge: coe glue Hom
-- statement:
--   The PAdic Hodge construction uses the coe glue Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWGlue.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWGlue.lean#L117-L119

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

theorem GroundTheory.PAdicHodge.coe_glueHom (i : ι) (x : Ω) (hx : (x : E) ∈ N i) :
    ((glueHom Ω N hN hdir hcov f hf x : Ω) : E) = ((f i ⟨x, hx⟩ : N i) : E) := by sorry
