-- Prove2me | Theorems.Thm_HoneycombCodes_lemma_D_6
-- name    : HoneycombCodes.lemma_D_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:55.069296+00:00
-- url     : https://prove2.me/theorems/1dc4c1eb-3de9-4c98-b46c-6c41a0dccec0
-- title:
--   Lemma D.6 — constant weight beats 2MQC when the mask is active
-- statement:
--   If a minimizing 2MQC point has $A<1$, then
--
--   $$
--   \kappa_{CW}(\delta)<R_{2MQC}(\delta). \tag{135}
--   $$
--
--   Differences from the source:
--
--   - encoding: '(u, v) minimize (127)' → IsR2MQCMinimizer δ u v: (u, v) ∈ F_δ and Ψ_δ(u, v) ≤ Ψ_δ at every point of F_δ; reason: the definition of a minimizer of (127)
--   - reading: the standing range of δ in Appendix D → hypotheses 0 < δ < 1/2; reason: App. D works throughout at 0 < δ < 1/2
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. D.4, Lemma D.6, eq. (135), p.64 (PDF 66)

import Mathlib
import Definitions.Def_HoneycombCodes_R2MQC
import Definitions.Def_HoneycombCodes_kappaCW

set_option autoImplicit false

namespace HoneycombCodes

/-- **Lemma D.6**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), App. D.4, p.64 (PDF 66). If a minimizing 2MQC point has `A < 1`, then
`κ_CW(δ) < R_2MQC(δ)` (135).

**Formalization Note.** Stated for `0 < δ < 1/2`; a minimizing 2MQC point is a minimizer of
(127) (`IsR2MQCMinimizer`) and `A = A_δ(u, v)`. -/
theorem lemma_D_6 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hA : ∃ u v : ℝ, IsR2MQCMinimizer δ u v ∧ Adelta δ u v < 1) :
    kappaCW δ < R2MQC δ := by sorry

end HoneycombCodes
