-- Prove2me | Theorems.Thm_GevreyGibbsSep_proposition_1
-- name    : GevreyGibbsSep.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:41:06.456702+00:00
-- url     : https://prove2.me/theorems/3220cc7b-a017-4186-8fcd-f10ea02e5c83
-- title:
--   Proposition 1 — the Gevrey bumps $p_{\nu,\ell,\alpha}$ are bumps with $\delta=(1+S)/(M+S)$ and barrier $\log\alpha$
-- statement:
--   Let $s>1$, $\alpha>1$, $0<\ell<2\pi$, $0<\nu\le\ell/4$, and put $M=(2\pi/\ell)^d$, $S=(\alpha-1)(1-2\nu/\ell)^d$. The bump distribution $p_{\nu,\ell,\alpha}$ (Definition 4), the Gibbs state of $\beta E_{\nu,\ell,\alpha}=-\log\bar p_{\nu,\ell,\alpha}$, satisfies:
--
--   1. it is a bump on the closed cell $\Omega_0=[0,\ell]^d\subset\mathbb T^d$ with background $\kappa=1/Z_{\nu,\ell,\alpha}$, where
--   $$\frac{Z_{\nu,\ell,\alpha}}{(2\pi)^d}=1+\frac SM\in[1,\alpha],\qquad \delta(\nu,\ell,\alpha)=p_{\nu,\ell,\alpha}(\Omega_0)=\frac{1+S}{M+S}>\frac{\mathrm{vol}(\Omega_0)}{(2\pi)^d};$$
--   2. its translates $p_g=p_{\nu,\ell,\alpha}(\cdot-g)$ are Gibbs states with $C^\infty$ periodic potentials satisfying $\beta\Delta=\log\alpha$.
--
--   These are the hard instances of the classical lower bound: a mesa of height ratio $\alpha$ hidden in a cell of side $\ell$.
--
--   **Formalization Note** The Gibbs state of $-\log\bar p_{\nu,\ell,\alpha}$ is shown to have density exactly $p_{\nu,\ell,\alpha}$ (and likewise for every translate). $\beta\Delta=\log\alpha$ is stated as: every difference of potential values is at most $\log\alpha$, with equality for some pair of points.
--
--   Differences from the source:
--   - encoding: dimension $d$ (a positive integer throughout the paper) → hypothesis $d\ge1$; reason: the paper's standing dimension; at $d=0$ the profile is constant and $\beta\Delta=0$
--   - encoding: translates by $g\in\mathbb T^d$ → translates by $g\in\mathbb R^d$; reason: every torus shift has a real lift
--   - encoding: $\beta\Delta=\log\alpha$ → $V(x)-V(y)\le\log\alpha$ for all $x,y$, with equality for some $x,y$; reason: the maximum minus the minimum of a continuous periodic function
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Proposition 1, Eq. (32), p.13; proof in Appendix B 3 b, p.40

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_toTorus
import Definitions.Def_GevreyGibbsSep_IsPeriodicSmooth
import Definitions.Def_GevreyGibbsSep_partitionFn
import Definitions.Def_GevreyGibbsSep_IsBump
import Definitions.Def_GevreyGibbsSep_bumpZ
import Definitions.Def_GevreyGibbsSep_bumpDensity
import Definitions.Def_GevreyGibbsSep_bumpPotential

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Proposition 1 (s-Gevrey bump family on `T^d`), arXiv:2608.24527 (sha256 d4fd40eb…), Eq. (32),
p.13. For `s > 1`, `α > 1`, `0 < ℓ < 2π`, `0 < ν ≤ ℓ/4`, with `M = (2π/ℓ)^d`,
`S = (α − 1)(1 − 2ν/ℓ)^d`: (1) `p_{ν,ℓ,α}` (the Gibbs state of `V = −log p̄_{ν,ℓ,α}`) is a bump
on `Ω₀ = [0, ℓ]^d` with `κ = 1/Z_{ν,ℓ,α}`, `Z_{ν,ℓ,α}/(2π)^d = 1 + S/M ∈ [1, α]` and
`δ = p_{ν,ℓ,α}(Ω₀) = (1 + S)/(M + S) > vol(Ω₀)/(2π)^d`; (2) its translates `p_g` are Gibbs states
with `C^∞` periodic potentials `V(· − g)` with `β∆ = log α`.

**Formalization Note** `d ≥ 1` is the paper's standing dimension (at `d = 0` the barrier is `0`). -/
theorem proposition_1 {d : ℕ} (hd : 0 < d) (s α ν ℓ : ℝ) (hs : 1 < s) (hα : 1 < α)
    (hℓ : 0 < ℓ) (hℓ2 : ℓ < 2 * Real.pi) (hν : 0 < ν) (hνℓ : ν ≤ ℓ / 4) :
    let V : (Fin d → ℝ) → ℝ := bumpPotential s ν ℓ α
    let M : ℝ := (2 * Real.pi / ℓ) ^ d
    let S : ℝ := (α - 1) * (1 - 2 * (ν / ℓ)) ^ d
    let Ω₀ : Set (Torus d) := toTorus '' Set.Icc (0 : Fin d → ℝ) (fun _ => ℓ)
    (∀ x, Real.exp (- V x) / partitionFn V = bumpDensity s ν ℓ α x) ∧
    IsBump V Ω₀ ((1 + S) / (M + S)) (1 / bumpZ d ν ℓ α) ∧
    bumpZ d ν ℓ α / (2 * Real.pi) ^ d = 1 + S / M ∧ 1 ≤ 1 + S / M ∧ 1 + S / M ≤ α ∧
    ∀ g : Fin d → ℝ,
      IsPeriodicSmooth (fun x => V (x - g)) ∧
      (∀ x, Real.exp (- V (x - g)) / partitionFn (fun y => V (y - g))
          = bumpDensity s ν ℓ α (x - g)) ∧
      (∀ x y, V (x - g) - V (y - g) ≤ Real.log α) ∧
      ∃ x y, V (x - g) - V (y - g) = Real.log α := by sorry

end GevreyGibbsSep
