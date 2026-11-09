-- Prove2me | Theorems.Thm_GevreyGibbsSep_theorem_B_2
-- name    : GevreyGibbsSep.theorem_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:41:26.955527+00:00
-- url     : https://prove2.me/theorems/7955b69f-3c68-4ad7-a611-e12fe7ab32fe
-- title:
--   Theorem B.2 — the bump potential lies in $\dot G^s(1/2,\rho_E)$ with barrier $\log\alpha$
-- statement:
--   Let $s>1$, $\alpha\ge e$, $0<\ell<2\pi$, $0<\nu\le\ell/4$, and let $\mathfrak r_s$ be the constant of (B38). The scaled potential of the bump,
--   $$\beta E_{\nu,\ell,\alpha}=-\log\bar p_{\nu,\ell,\alpha}=-F+\log Z_{\nu,\ell,\alpha},$$
--   is a $2\pi$-periodic $C^\infty$ function in $\dot G^s(\xi_E,\rho_E)$ with
--   $$\xi_E=\frac12,\qquad \rho_E=\frac{\mathfrak r_s\,\nu}{2\,d^s(\log\alpha)^s},$$
--   and its barrier amplitude is $e^{\beta\Delta}=\alpha$.
--
--   This certifies that the hard instances lie in the class $\mathscr W^s(\alpha,\xi,\rho)$ for $\xi\ge1/2$, $\rho\le\rho_E$; the radius is linear in the ramp width $\nu$.
--
--   Differences from the source:
--   - encoding: dimension $d$ → hypothesis $d\ge1$; reason: the paper's standing dimension
--   - encoding: barrier amplitude $\alpha=e^{\beta\Delta}$ → $V(x)-V(y)\le\log\alpha$ for all $x,y$, with equality for some $x,y$; reason: the same statement about the range of the potential
--   - reading: "the bump" (Definition 4) → the ranges $0<\ell<2\pi$, $0<\nu\le\ell/4$ of Definition 4 as hypotheses; reason: the theorem refers to the bump of Definition 4, which is defined for these parameters
--   - encoding: $\beta E\in\dot G^s(\xi_E,\rho_E)$, the supremum in (3) over $x\in[0,2\pi)^d$ → $|\partial^aV(x)|\,\rho_E^{\|a\|_1}\le\xi_E\,(a!)^s$ for every $a\ne0$ and every $x\in\mathbb R^d$; reason: the same bound for a $2\pi$-periodic function
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem B.2, Eqs. (B71)–(B72), p.45; (33), p.14

import Mathlib
import Definitions.Def_GevreyGibbsSep_IsPeriodicSmooth
import Definitions.Def_GevreyGibbsSep_InDotGevrey
import Definitions.Def_GevreyGibbsSep_bumpPotential
import Definitions.Def_GevreyGibbsSep_rs

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Theorem B.2 (Gevrey seminorm of the bump potential), arXiv:2608.24527 (sha256 d4fd40eb…),
Eqs. (B71)–(B72), p.45. For `s > 1`, `α ≥ e`, `0 < ℓ < 2π`, `0 < ν ≤ ℓ/4`, the scaled potential
`βE_{ν,ℓ,α} = −log p̄_{ν,ℓ,α}` is a `2π`-periodic `C^∞` function in `Ġ^s(ξ_E, ρ_E)` with
`ξ_E = 1/2`, `ρ_E = r_s ν/(2 d^s (log α)^s)`, and its barrier amplitude is `e^{β∆} = α`.

**Formalization Note** `d ≥ 1` is the paper's standing dimension. "Barrier amplitude `α`" is
stated as `V x − V y ≤ log α` for all `x, y`, with equality for some `x, y`. -/
theorem theorem_B_2 {d : ℕ} (hd : 0 < d) (s α ν ℓ : ℝ) (hs : 1 < s) (hα : Real.exp 1 ≤ α)
    (hℓ : 0 < ℓ) (hℓ2 : ℓ < 2 * Real.pi) (hν : 0 < ν) (hνℓ : ν ≤ ℓ / 4) :
    let V : (Fin d → ℝ) → ℝ := bumpPotential s ν ℓ α
    IsPeriodicSmooth V ∧
    InDotGevrey s (1 / 2) (rs s * ν / (2 * (d : ℝ) ^ s * Real.log α ^ s)) V ∧
    (∀ x y, V x - V y ≤ Real.log α) ∧ ∃ x y, V x - V y = Real.log α := by sorry

end GevreyGibbsSep
