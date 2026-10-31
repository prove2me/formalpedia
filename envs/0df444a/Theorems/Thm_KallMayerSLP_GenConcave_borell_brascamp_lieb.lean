-- Prove2me | Theorems.Thm_KallMayerSLP_GenConcave_borell_brascamp_lieb
-- name    : KallMayerSLP.GenConcave.borell_brascamp_lieb
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:32.566825+00:00
-- url     : https://prove2.me/theorems/427e7df9-ba54-4367-84c0-bc08d6eaec79
-- title:
--   The integral inequality of the proof of Theorem 2.8 (Borell–Brascamp–Lieb)
-- statement:
--   Let $r\ge 1$, $-1/r\le\gamma\le\infty$ and $\lambda\in[0,1]$. Let $f,g,h:\mathbb R^r\to\mathbb R_+$, with $f$ and $g$ integrable and $h$ measurable, satisfy
--
--   $$
--   h(\lambda x+(1-\lambda)y)\ \ge\ \mathcal M_\gamma^\lambda\bigl(f(x),g(y)\bigr)\qquad\text{for all }x,y\in\mathbb R^r.
--   $$
--
--   Then
--
--   $$
--   \int_{\mathbb R^r} h(z)\,dz\ \ge\ \mathcal M^\lambda_{\gamma/(1+r\gamma)}\Bigl(\int_{\mathbb R^r} f(x)\,dx,\ \int_{\mathbb R^r} g(y)\,dy\Bigr),
--   $$
--
--   where $\gamma/(1+r\gamma)$ is $-\infty$ at $\gamma=-1/r$ and $1/r$ at $\gamma=\infty$.
--
--   For $\gamma=0$ this is Prékopa's (Prékopa–Leindler) inequality. The book applies it to $f\mathbf 1_A$, $f\mathbf 1_B$ and $f\mathbf 1_{\lambda A+(1-\lambda)B}$ for a $\gamma$-concave density $f$, which proves Theorem 2.8.
--
--   **Formalization Note** $\mathbb R^r$ is `Fin r → ℝ` with Lebesgue measure. The integral of $h$ is taken in $[0,\infty]$, so $h$ need not be integrable (if $\int h=\infty$ the claim is trivial); $h$ is assumed a.e.-measurable so that its integral is defined.
--
--   Differences from the source:
--   - reading: "an integral–inequality, see Prékopa [234]" applied to $f\mathbf 1_A$, $f\mathbf 1_B$ and the pointwise supremum of $\mathcal M_\gamma^\lambda(f(x),f(y))$ over $\lambda x+(1-\lambda)y=z$ → the general inequality for integrable $f,g\ge 0$ and a measurable $h\ge 0$ dominating $\mathcal M_\gamma^\lambda(f(x),g(y))$; reason: the book cites the inequality without stating it; this is its standard form, and the book's chain is the case $h=f\mathbf 1_{\lambda A+(1-\lambda)B}$
--   - generalization: $\int h$ a real number → $\int h\in[0,\infty]$, $h$ not assumed integrable; reason: specializes to integrable $h$
--   - encoding: $\gamma/(1+r\gamma)$ at $\gamma=-1/r$ and $\gamma=\infty$ → $-\infty$ and $1/r$; reason: the formula is undefined there; the limits are the values of Figure 2.6 (paper reading 4)
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, proof of Theorem 2.8, p.127 (PDF 137) (cited from Prékopa [234])

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_genMean
import Definitions.Def_KallMayerSLP_GenConcave_concavityExponent

open MeasureTheory

namespace KallMayerSLP.GenConcave

/-- **The integral inequality used in the proof of Theorem 2.8** (Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 2, proof of Theorem 2.8, p. 127,
PDF p. 137; "an integral-inequality, see Prékopa [234] (for `γ = 0` it is called Prékopa's
inequality)"; Borell–Brascamp–Lieb). Let `r ≥ 1`, `−1/r ≤ γ ≤ ∞`, `λ ∈ [0, 1]`, and let
`f, g, h : ℝ^r → ℝ₊` with `f`, `g` integrable and `h` measurable satisfy
`h(λx + (1 − λ)y) ≥ M_γ^λ(f(x), g(y))` for all `x, y ∈ ℝ^r`. Then
`∫ h ≥ M_{γ/(1+rγ)}^λ(∫ f, ∫ g)`.

**Formalization Note.** `ℝ^r = Fin r → ℝ` with Lebesgue measure `volume`; `γ ∈ EReal` and
`γ/(1 + rγ)` is `concavityExponent r γ` (`−∞` at `γ = −1/r`, `1/r` at `γ = ∞`). The
integral of `h` is the lower Lebesgue integral `∫⁻` in `[0, ∞]`, so `h` need not be
integrable; `h` is assumed a.e.-measurable so that its integral is defined. The book uses the
inequality with `f = 𝟙_A f₀`, `g = 𝟙_B f₀`, `h = 𝟙_{λA+(1−λ)B} f₀` for a density `f₀`. -/
theorem borell_brascamp_lieb {r : ℕ} (hr : 0 < r) (γ : EReal)
    (hγ : (((-1 : ℝ) / r : ℝ) : EReal) ≤ γ) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (f g h : (Fin r → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Integrable f) (hg : Integrable g) (hh : AEMeasurable h)
    (hfgh : ∀ x y : Fin r → ℝ, genMean γ lam (f x) (g y) ≤ h (lam • x + (1 - lam) • y)) :
    ENNReal.ofReal (genMean (concavityExponent r γ) lam (∫ x, f x) (∫ x, g x)) ≤
      ∫⁻ x, ENNReal.ofReal (h x) := by sorry

end KallMayerSLP.GenConcave
