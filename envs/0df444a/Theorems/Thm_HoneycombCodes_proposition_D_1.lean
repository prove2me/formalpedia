-- Prove2me | Theorems.Thm_HoneycombCodes_proposition_D_1
-- name    : HoneycombCodes.proposition_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:46.952333+00:00
-- url     : https://prove2.me/theorems/7f537f26-4add-4c1e-8a81-51bf6046be03
-- title:
--   Proposition D.1 — the whole-cube exponent equals MQC
-- statement:
--   For every $0<\delta<1/2$,
--
--   $$
--   \kappa_H(\delta)=R_{MQC}(\delta). \tag{120}
--   $$
--
--   More explicitly, if $\sigma=1-2\delta$ and $u\in[\sigma,1]$, the closed whole-cube spectral boundary is
--
--   $$
--   a=J(u^2),\qquad b=J\bigl(u(u-\sigma)\bigr); \tag{121}
--   $$
--
--   at this point $\Gamma_H(a,b)=\sigma$ and the objective $H_2(a)-H_2(b)$ equals the integrand $g(u^2)-g(u(u-\sigma))$ of (119).
--
--   This identifies OpenAI's whole-cube bound with Alrabiah–Guruswami's mixed-qubit-channel bound.
--
--   Differences from the source:
--
--   - reading: the MQC and 2MQC exponents of [AG26] (recalled in Appendix D) → R_MQC and R_2MQC defined by the paper's normalized displays (119) and (122)–(124), with λ_δ(0,0) = 2δ; reason: Theorem 1.2 refers to App. D for these exponents; the normalized displays are the only definitions this paper states
--   - reading: 'the closed whole-cube spectral boundary is a = J(u²), b = J(u(u − σ))' → the point satisfies 0 ≤ b ≤ a ≤ 1/2 and Γ_H(a, b) = σ; reason: membership in the closed whole-cube region together with equality in the spectral constraint
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. D.1, Proposition D.1, eqs. (120)–(121), p.59 (PDF 61)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaH
import Definitions.Def_HoneycombCodes_RMQC

set_option autoImplicit false

namespace HoneycombCodes

/-- **Proposition D.1**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), App. D.1, p.59 (PDF 61). For every `0 < δ < 1/2`,
`κ_H(δ) = R_MQC(δ)` (120). More explicitly, if `σ = 1 − 2δ` and `u ∈ [σ, 1]`, the closed
whole-cube spectral boundary is `a = J(u²)`, `b = J(u(u − σ))` (121); at this point
`Γ_H(a, b) = σ` and the objective equals the integrand in (119).

**Formalization Note.** "The closed whole-cube spectral boundary" is rendered as: the point lies
in `0 ≤ b ≤ a ≤ 1/2` and has `Γ_H(a, b) = σ`; the objective `H₂(a) − H₂(b)` equals
`g(u²) − g(u(u − σ))`. -/
theorem proposition_D_1 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    kappaH δ = RMQC δ ∧
    ∀ u ∈ Set.Icc (1 - 2 * δ) 1,
      0 ≤ Jmap (u * (u - (1 - 2 * δ))) ∧ Jmap (u * (u - (1 - 2 * δ))) ≤ Jmap (u ^ 2) ∧
      Jmap (u ^ 2) ≤ 1 / 2 ∧
      GammaH (Jmap (u ^ 2)) (Jmap (u * (u - (1 - 2 * δ)))) = 1 - 2 * δ ∧
      H2 (Jmap (u ^ 2)) - H2 (Jmap (u * (u - (1 - 2 * δ)))) =
        g (u ^ 2) - g (u * (u - (1 - 2 * δ))) := by sorry

end HoneycombCodes
