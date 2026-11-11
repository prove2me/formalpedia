-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_claim_4_13
-- name    : LabelSymmetricCollision215.Collision.claim_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:47.036199+00:00
-- url     : https://prove2.me/theorems/412c72e5-bd9a-48f6-b521-ad61331d0e68
-- title:
--   Claim 4.13 — Tensor-sector identification
-- statement:
--   For every algorithm product-basis value $\eta$ and occupied set $I$, let $V_{\eta,I}$ read its occupied values in increasing address order. Both identities hold on the whole joint space after the sector projection:
--   $$V_{\eta,I}\Pi_{\rm Comp}\Lambda_{\eta,I}=\Pi_{W^{\otimes|I|}}V_{\eta,I}\Lambda_{\eta,I},$$
--   $$V_{\eta,I}\Pi_{=0}\Lambda_{\eta,I}=\Pi_{C_{|I|}^\perp}V_{\eta,I}\Lambda_{\eta,I}.$$
--   These identify the physical database constraints with the tensor constraints.
--
--   Differences from the source:
--   - encoding: sector-restricted map V and both projected identities → the sector map extended by zero to other sectors; reason: both sides already precompose with the exact sector projector, so the extension changes no source instance
--   - generalization: occupied set I = {i1 < ... < is} with s ≥ 1 (Definition 4.5 context) → every occupied set I ⊆ [M], including I = ∅ (zeroth tensor power); reason: for I = ∅ both identities hold trivially (both projections act as the identity on the one-dimensional sector); for |I| ≥ 1 the Lean statement is exactly the source claim
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Claim 4.13, PDF 29 / printed 27

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Claim 4.13, PDF 29 / printed 27. -/
theorem claim_4_13 {M N : ℕ} {W : Type} [Fintype W] [NeZero N] (hM : 0 < M)
    (η : Reg M N W) (I : Finset (Fin M)) :
    (sectorMap η I).comp ((compressedProjection M N W).comp (sectorProjection η I)) =
      (wTensor N I.card).starProjection.comp ((sectorMap η I).comp (sectorProjection η I)) ∧
    (sectorMap η I).comp ((freeProjection M N W).comp (sectorProjection η I)) =
      (freeTensor N I.card).starProjection.comp ((sectorMap η I).comp (sectorProjection η I)) := by sorry

end LabelSymmetricCollision215.Collision
