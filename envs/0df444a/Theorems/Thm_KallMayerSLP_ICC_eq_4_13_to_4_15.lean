-- Prove2me | Theorems.Thm_KallMayerSLP_ICC_eq_4_13_to_4_15
-- name    : KallMayerSLP.ICC.eq_4_13_to_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:33.444988+00:00
-- url     : https://prove2.me/theorems/37d8969f-14e8-4c59-bed0-f4e852043dc1
-- title:
--   (4.13)–(4.15) — the $\alpha$-variant is equivalent to $K_\alpha(x)\le 0$, and $K_\alpha$ is convex or concave
-- statement:
--   Let $\xi$ have law $P$, suppose the expected values of $t(\xi)$ and $h(\xi)$ exist, and put $\bar t=\mathbb E_\xi[t(\xi)]$, $\bar h=\mathbb E_\xi[h(\xi)]$. For every $\alpha\in\mathbb R$ and every $x$, the three conditions
--   $$
--   \mathbb E_\xi[\zeta^+(x,\xi)]\le\alpha\,\mathbb E_\xi[|\zeta(x,\xi)|],
--   $$
--   $$
--   (1-2\alpha)\mathbb E_\xi[\zeta^+(x,\xi)]+\alpha\,\mathbb E_\xi[\zeta(x,\xi)]\le 0,
--   $$
--   $$
--   (1-2\alpha)\mathbb E_\xi[\zeta^+(x,\xi)]+\alpha(\bar t x-\bar h)\le 0
--   $$
--   are equivalent. Moreover:
--
--   1. $K_\alpha(x)=(1-\alpha)K(x)-\alpha H(x)$, so $K_\alpha$ is the evaluation of $\rho^\alpha_{\mathrm{sic}}$ at $\zeta(x,\xi)$;
--   2. $K_\alpha$ is convex for $\alpha<\tfrac12$;
--   3. $K_\alpha$ is concave for $\alpha>\tfrac12$;
--   4. for $\alpha=\tfrac12$, $K_\alpha(x)=\alpha(\bar t x-\bar h)$ is linear-affine.
--
--   The sign of $1-2\alpha$ is what makes the constraint convex or not, and it is why the polyhedral representation below needs $\alpha\le\tfrac12$.
--
--   Differences from the source:
--
--   - generalization: ξ is a random vector in ℝʳ, t(ξ), h(ξ) affine in ξ (1.2), law ℙ_ξ → Ξ any measurable space, P any probability measure on Ξ, t, h arbitrary functions with integrable components; reason: the book says (1.2) is not used in the chapter; Ξ = ℝʳ with P = ℙ_ξ gives the book's case
--   - generalization: α prescribed, with the remark that α ∈ [0, 1] suffices → every real α; reason: the identities hold for all α; [0, 1] is a special case
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, (4.13)–(4.15), p.153 (PDF 163), and p.154 (PDF 164)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_K
import Definitions.Def_KallMayerSLP_ICC_H
import Definitions.Def_KallMayerSLP_ICC_KAlpha

open MeasureTheory Matrix

namespace KallMayerSLP.ICC

/-- **The `α`-variant (4.13)–(4.15) and the shape of `K_α`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, (4.13)–(4.15), p.153 (PDF 163),
and p.154 (PDF 164). The inequality `𝔼_ξ[ζ⁺] ≤ α 𝔼_ξ[|ζ|]` (4.13) can be equivalently written as
`(1 − 2α)𝔼_ξ[ζ⁺] + α 𝔼_ξ[ζ] ≤ 0` (4.14) or as `(1 − 2α)𝔼_ξ[ζ⁺] + α(t̄x − h̄) ≤ 0` (4.15). Also
`K_α = (1 − α)K − αH`, the evaluation of `ρ^α_sic = (1 − α)𝔼[ϑ⁺] − α𝔼[ϑ⁻]` at `ζ(x, ξ)`; `K_α` is
convex for `α < ½`, concave for `α > ½`, and linear-affine for `α = ½`.

**Formalization Note.** No sign restriction on `α` is needed; the book's remark that `α ∈ [0, 1]`
suffices is a remark on which `α` give interesting constraints. `ht`, `hh` are the standing
assumption of §4.1 (p.149). -/
theorem eq_4_13_to_4_15 {Ξ : Type*} [MeasurableSpace Ξ] {n : ℕ} (P : Measure Ξ)
    [IsProbabilityMeasure P] (t : Ξ → Fin n → ℝ) (h : Ξ → ℝ)
    (ht : ∀ j, Integrable (fun ξ => t ξ j) P) (hh : Integrable h P) (α : ℝ) :
    (∀ x, (K P t h x ≤ α * ∫ ξ, |zeta t h x ξ| ∂P ↔
        (1 - 2 * α) * K P t h x + α * ∫ ξ, zeta t h x ξ ∂P ≤ 0) ∧
      ((1 - 2 * α) * K P t h x + α * ∫ ξ, zeta t h x ξ ∂P ≤ 0 ↔
        (1 - 2 * α) * K P t h x + α * ((∫ ξ, t ξ ∂P) ⬝ᵥ x - ∫ ξ, h ξ ∂P) ≤ 0)) ∧
    (∀ x, KAlpha P t h α x = (1 - α) * K P t h x - α * H P t h x) ∧
    (α < 1 / 2 → ConvexOn ℝ Set.univ (KAlpha P t h α)) ∧
    (1 / 2 < α → ConcaveOn ℝ Set.univ (KAlpha P t h α)) ∧
    (α = 1 / 2 → ∀ x, KAlpha P t h α x = α * ((∫ ξ, t ξ ∂P) ⬝ᵥ x - ∫ ξ, h ξ ∂P)) := by sorry

end KallMayerSLP.ICC
