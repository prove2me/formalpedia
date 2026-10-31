-- Prove2me | Theorems.Thm_KallMayerSLP_ICC_proposition_4_2
-- name    : KallMayerSLP.ICC.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:28.144749+00:00
-- url     : https://prove2.me/theorems/be64ed79-be7c-46fa-8353-7880ef67af5f
-- title:
--   Proposition 4.2 — $H$, $K$ and $\mathbb E_\xi|\zeta|=H+K$ are convex
-- statement:
--   Let $\xi$ have law $P$, and suppose the expected values of $t(\xi)\in\mathbb R^n$ and $h(\xi)\in\mathbb R$ exist. Then the functions $H(x)=\mathbb E_\xi[\zeta^-(x,\xi)]$ and $K(x)=\mathbb E_\xi[\zeta^+(x,\xi)]$ are convex on $\mathbb R^n$, and consequently so is
--   $$
--   \mathbb E_\xi[|\zeta(x,\xi)|]=H(x)+K(x).
--   $$
--   No other assumption on the distribution is made. This contrasts with probability functions, whose generalized concavity needs restrictive distributional assumptions and fails for finite discrete distributions in general.
--
--   Differences from the source:
--
--   - generalization: ξ is a random vector in ℝʳ, t(ξ), h(ξ) affine in ξ (1.2), law ℙ_ξ → Ξ any measurable space, P any probability measure on Ξ, t, h arbitrary functions with integrable components; reason: the book says (1.2) is not used in the chapter; Ξ = ℝʳ with P = ℙ_ξ gives the book's case
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Proposition 4.2, p.150 (PDF 160)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_K
import Definitions.Def_KallMayerSLP_ICC_H

open MeasureTheory

namespace KallMayerSLP.ICC

/-- **Proposition 4.2 (separate integrated probability functions are convex).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, Proposition 4.2, p.150 (PDF 160).
`H(x)` and `K(x)`, and consequently `𝔼_ξ[|ζ(x, ξ)|] = H(x) + K(x)`, are convex functions on `ℝⁿ`.

**Formalization Note.** The standing assumption of §4.1 (p.149), that the expected values of `t(ξ)`
and `h(ξ)` exist, is `ht` and `hh`; there is no other restriction on the law `P` of `ξ`. The
identity is stated as its own clause. -/
theorem proposition_4_2 {Ξ : Type*} [MeasurableSpace Ξ] {n : ℕ} (P : Measure Ξ)
    [IsProbabilityMeasure P] (t : Ξ → Fin n → ℝ) (h : Ξ → ℝ)
    (ht : ∀ j, Integrable (fun ξ => t ξ j) P) (hh : Integrable h P) :
    ConvexOn ℝ Set.univ (H P t h) ∧
    ConvexOn ℝ Set.univ (K P t h) ∧
    (∀ x, ∫ ξ, |zeta t h x ξ| ∂P = H P t h x + K P t h x) ∧
    ConvexOn ℝ Set.univ (fun x => ∫ ξ, |zeta t h x ξ| ∂P) := by sorry

end KallMayerSLP.ICC
