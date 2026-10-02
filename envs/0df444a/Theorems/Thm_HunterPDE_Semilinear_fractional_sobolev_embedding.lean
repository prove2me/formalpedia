-- Prove2me | Theorems.Thm_HunterPDE_Semilinear_fractional_sobolev_embedding
-- name    : HunterPDE.Semilinear.fractional_sobolev_embedding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:13:59.770335+00:00
-- url     : https://prove2.me/theorems/b9d0a7f8-9df5-4423-8969-ab641335e00e
-- title:
--   Theorem 5.79 — Sobolev embedding for Hˢ(ℝⁿ): into L^q for s < n/2, into C₀ for s > n/2
-- statement:
--   Let $H^s(\mathbb{R}^n)$ be the fractional $L^2$-Sobolev space.
--
--   1. If $0 < s < n/2$ and $q$ is given by $\dfrac1q = \dfrac12 - \dfrac sn$, then $H^s(\mathbb{R}^n) \hookrightarrow L^q(\mathbb{R}^n)$ and there is a constant $C = C(n,s)$ such that
--   $$\|f\|_{L^q} \le C\,\|f\|_{H^s} \qquad \text{for every } f \in H^s.$$
--   2. If $n/2 < s < \infty$, then $H^s(\mathbb{R}^n) \hookrightarrow C_0(\mathbb{R}^n)$ and there is a constant $C = C(n,s)$ such that
--   $$\|f\|_{L^\infty} \le C\,\|f\|_{H^s} \qquad \text{for every } f \in H^s.$$
--
--   The second part is what makes the nonlinearity $F(h) = \lambda h - \gamma h^m$ locally Lipschitz from $H^{2\alpha}$ to $L^2$ when $\alpha > n/4$.
--
--   **Formalization Note.** $f$ is complex-valued, and $f \in H^s$ is `hsNorm n s f < ⊤`. $f \in C_0$ means $f$ agrees almost everywhere with a continuous function tending to $0$ at infinity. The page prints both inequalities without $C$ on the right-hand side although it announces the constant $C = C(n,s)$; the constant is restored. $C$ is chosen after $n, s$ (and $q$) and before $f$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 175, Theorem 5.79

import Mathlib
import Definitions.Def_HunterPDE_Semilinear_SobolevHs

open MeasureTheory Filter
open scoped ENNReal Topology

namespace HunterPDE.Semilinear

/-- Theorem 5.79 of Hunter, *Notes on PDEs* (p. 175), the Sobolev embedding theorem for the
fractional `L²`-Sobolev spaces `Hˢ(ℝⁿ)`:

1. If `0 < s < n/2` and `1/q = 1/2 − s/n`, then `Hˢ(ℝⁿ) ↪ L^q(ℝⁿ)` and there is a constant
   `C = C(n, s)` such that `‖f‖_{L^q} ≤ C ‖f‖_{Hˢ}`.
2. If `n/2 < s < ∞`, then `Hˢ(ℝⁿ) ↪ C₀(ℝⁿ)` and there is a constant `C = C(n, s)` such that
   `‖f‖_{L^∞} ≤ C ‖f‖_{Hˢ}`.

The page prints both inequalities without the `C` on the right-hand side; the constant it
announces is restored. `f ∈ Hˢ(ℝⁿ)` is `hsNorm n s f < ∞` (complex-valued `f`), and
`f ∈ C₀(ℝⁿ)` means that `f` agrees almost everywhere with a continuous function tending to `0`
at infinity. -/
theorem fractional_sobolev_embedding (n : ℕ) :
    (∀ s q : ℝ, 0 < s → s < (n : ℝ) / 2 → 1 / q = 1 / 2 - s / n →
      ∃ C : ℝ, ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, hsNorm n s f < ⊤ →
        MemLp f (ENNReal.ofReal q) volume ∧
        eLpNorm f (ENNReal.ofReal q) volume ≤ ENNReal.ofReal C * hsNorm n s f) ∧
    (∀ s : ℝ, (n : ℝ) / 2 < s →
      ∃ C : ℝ, ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, hsNorm n s f < ⊤ →
        (∃ f₀ : EuclideanSpace ℝ (Fin n) → ℂ, Continuous f₀ ∧
          Tendsto f₀ (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) ∧ f =ᵐ[volume] f₀) ∧
        eLpNorm f ⊤ volume ≤ ENNReal.ofReal C * hsNorm n s f) := by sorry

end HunterPDE.Semilinear
