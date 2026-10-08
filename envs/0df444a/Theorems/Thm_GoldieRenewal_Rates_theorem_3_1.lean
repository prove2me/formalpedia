-- Prove2me | Theorems.Thm_GoldieRenewal_Rates_theorem_3_1
-- name    : GoldieRenewal.Rates.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:10:17.983142+00:00
-- url     : https://prove2.me/theorems/ea301ff5-164d-4ff3-a856-5605109f10ca
-- title:
--   Theorem 3.1 — explicit-rate Stone decomposition ν = ν₀ + ν₁ with p(t) = 1/m − (1/2π)∮ e^{−iθt}dθ/(1 − η̂(θ)) + o(e^{−βt})
-- statement:
--   Let $\eta$ be a probability law on $\mathbb R$ with finite second moment and positive first moment $m$, such that $\tilde\eta(\beta)<\infty$ for some $\beta>0$. Suppose that for some $n_0$
--   $$\eta^{(n_0)}=(1-\delta)\varphi_0+\delta\varphi_1,$$
--   where $\delta\in[0,1)$ and $\varphi_0,\varphi_1$ are probability measures with $\varphi_0$ absolutely continuous, that $\delta\tilde\varphi_1(\beta)<1$, and that $\hat\eta(\theta)\neq1$ on $\Im\theta=-\beta$.
--
--   Then the renewal measure $\nu=\sum_{n\ge0}\eta^{(n)}$ can be written $\nu=\nu_0+\nu_1$, where $\nu_1$ is a finite measure with $\tilde\nu_1(\beta)<\infty$ and $\nu_0$ is absolutely continuous with a continuous bounded density $p$ such that
--   $$p(t)=\frac1m-\frac1{2\pi}\oint_{\mathscr C}e^{-i\theta t}\frac{d\theta}{1-\hat\eta(\theta)}+o(e^{-\beta t}),\qquad t\to\infty,$$
--   for every positively oriented rectangle contour $\mathscr C$ whose closure lies in $D=\{-\beta<\Im\theta<0\}$ and which encloses all zeros of $1-\hat\eta$ in $D$.
--
--   This sharpens Stone's (1966) decomposition of a renewal measure by an exponential remainder and an explicit finite sum of oscillating terms coming from the zeros of $1-\hat\eta$ in the strip.
--
--   **Formalization Note** The contour $\mathscr C$ of the paper ("a simple closed contour in $D$ enclosing all the zeroes of $1-\hat\eta$ in $D$") is encoded as the boundary of an admissible rectangle; the expansion is stated for every such rectangle, as a complex identity (the contour term is real, so no real part is taken, as in the paper). The density is nonnegative and $\nu_0$ is Lebesgue measure with density $p$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 131, Theorem 3.1, (3.1)–(3.2)

import Mathlib
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_GoldieRenewal_Rates_Transforms

open MeasureTheory Complex Filter Asymptotics

namespace GoldieRenewal.Rates

/-- **Theorem 3.1** (Goldie 1991, p. 131; explicit-rate Stone decomposition). Let `η` be a
probability law on `ℝ` with finite second moment and positive first moment `m`, such that
`η̃(β) < ∞` for some `β > 0`, satisfying (3.1) and the subsequent conditions (`StoneConditions`).
Then the renewal measure `ν = Σ η^{(n)}` splits as `ν = ν₀ + ν₁` with `ν₁` finite,
`ν̃₁(β) < ∞`, and `ν₀` absolutely continuous with a continuous bounded density `p` such that
(3.2) `p(t) = 1/m − (1/2π) ∮_𝒞 e^{−iθt} dθ / (1 − η̂(θ)) + o(e^{−βt})`, `t → ∞`.
Formalization Note: `𝒞` is any positively oriented rectangle boundary admissible in the sense
of `EnclosesZerosInStrip` (closed rectangle inside `D = {−β < ℑθ < 0}`, all zeros of `1 − η̂`
in `D` inside the open rectangle); the identity is stated for every such rectangle, as a
complex identity (the paper writes no real part; the contour term is real). The density is
nonnegative and `ν₀ = p · Lebesgue`. -/
theorem theorem_3_1 (η : Measure ℝ) [IsProbabilityMeasure η] (β : ℝ) (hβ : 0 < β)
    (h_second : Integrable (fun x : ℝ => x ^ 2) η)
    (h_mean : 0 < ∫ x, x ∂η)
    (h_exp : expTransform η β < ⊤)
    (h_stone : StoneConditions η β) :
    ∃ (ν₀ ν₁ : Measure ℝ) (p : ℝ → ℝ),
      renewalMeasure η = ν₀ + ν₁ ∧
      IsFiniteMeasure ν₁ ∧ expTransform ν₁ β < ⊤ ∧
      ν₀ = volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      (∀ x, 0 ≤ p x) ∧ Continuous p ∧ (∃ C : ℝ, ∀ x, |p x| ≤ C) ∧
      ∀ z w : ℂ, EnclosesZerosInStrip (fun θ => 1 - charTransform η θ) β z w →
        (fun t : ℝ => (p t : ℂ) -
            ((1 / (∫ x, x ∂η) : ℝ) - (1 / (2 * Real.pi : ℂ)) *
              RectangleIntegral
                (fun θ : ℂ => Complex.exp (-(I * θ * (t : ℂ))) / (1 - charTransform η θ)) z w))
          =o[atTop] (fun t : ℝ => Real.exp (-(β * t))) := by sorry

end GoldieRenewal.Rates
