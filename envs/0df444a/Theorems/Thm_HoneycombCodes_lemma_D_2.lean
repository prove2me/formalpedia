-- Prove2me | Theorems.Thm_HoneycombCodes_lemma_D_2
-- name    : HoneycombCodes.lemma_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:14.875208+00:00
-- url     : https://prove2.me/theorems/b09aee9a-caf3-4e61-adc1-0a3bf8f0fce2
-- title:
--   Lemma D.2 — compactification of the 2MQC problem
-- statement:
--   Let
--
--   $$
--   F_\delta=\bigl\{(u,v): 0\le v\le u\le 1,\ v^2(u^2-v^2)\le 2\delta u^2(1-v^2)\bigr\}. \tag{126}
--   $$
--
--   Then $\Psi_\delta$ is continuous on $F_\delta$ and
--
--   $$
--   R_{2MQC}(\delta)=\min_{(u,v)\in F_\delta}\Psi_\delta(u,v). \tag{127}
--   $$
--
--   **Formalization Note** Stated for $0<\delta<1/2$, the standing range of Appendix D; the minimum is attained.
--
--   Differences from the source:
--
--   - reading: the MQC and 2MQC exponents of [AG26] (recalled in Appendix D) → R_MQC and R_2MQC defined by the paper's normalized displays (119) and (122)–(124), with λ_δ(0,0) = 2δ; reason: Theorem 1.2 refers to App. D for these exponents; the normalized displays are the only definitions this paper states
--   - reading: the standing range of δ in Appendix D → hypotheses 0 < δ < 1/2; reason: App. D works throughout at 0 < δ < 1/2 (Theorem D.8)
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. D.2, Lemma D.2, eqs. (126)–(127), p.61 (PDF 63)

import Mathlib
import Definitions.Def_HoneycombCodes_R2MQC

set_option autoImplicit false

namespace HoneycombCodes

/-- **Lemma D.2**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), App. D.2, p.61 (PDF 63). Let
`F_δ = {(u, v) : 0 ≤ v ≤ u ≤ 1, v²(u² − v²) ≤ 2δu²(1 − v²)}` (126). Then `Ψ_δ` is continuous on
`F_δ` and `R_2MQC(δ) = min_{(u, v) ∈ F_δ} Ψ_δ(u, v)` (127).

**Formalization Note.** Stated for `0 < δ < 1/2`, the standing range of App. D. "min" is attained:
some point of `F_δ` has value `R_2MQC(δ)` and no point of `F_δ` has a smaller value. -/
theorem lemma_D_2 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ContinuousOn (fun p : ℝ × ℝ => PsiDelta δ p.1 p.2) (Fset δ) ∧
    (∃ p ∈ Fset δ, PsiDelta δ p.1 p.2 = R2MQC δ) ∧
    (∀ p ∈ Fset δ, R2MQC δ ≤ PsiDelta δ p.1 p.2) := by sorry

end HoneycombCodes
