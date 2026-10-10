-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_energy_estimates
-- name    : HunterPDE.Elliptic.energy_estimates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:48:41.917352+00:00
-- url     : https://prove2.me/theorems/96a8ec24-f4b3-49b1-a6c3-b5c77cb8f2fd
-- title:
--   Theorem 4.21 — Gårding's inequality and boundedness of the bilinear form, with explicit γ
-- statement:
--   Let $a$ be the bilinear form (4.20) on $H^1_0(\Omega)$, where the coefficients satisfy (4.17) and the uniform ellipticity condition (4.18) with constant $\theta > 0$. Then there are constants $C_1, C_2 > 0$ and $\gamma \in \mathbb{R}$ such that for all $u, v \in H^1_0(\Omega)$
--   $$C_1\|u\|_{H^1_0}^2 \le a(u,u) + \gamma\|u\|_{L^2}^2, \qquad |a(u,v)| \le C_2\|u\|_{H^1_0}\|v\|_{H^1_0}.$$
--   If $b = 0$ one may take $\gamma = \theta - c_0$, where $c_0 = \inf_\Omega c$; if $b \ne 0$ one may take
--   $$\gamma = \frac{1}{2\theta}\sum_{i=1}^n \|b_i\|_{L^\infty}^2 + \frac{\theta}{2} - c_0 .$$
--
--   The first estimate (Gårding's inequality) is the coercivity that Lax–Milgram needs after a shift by $\gamma$; the second is boundedness of the form.
--
--   **Formalization Note.** $\|u\|_{H^1_0}$ is the standard norm (4.13). The explicit $\gamma$ is asserted for **every** $c_0$ with $c \ge c_0$ a.e. in $\Omega$, including $c_0 = \operatorname{ess\,inf}_\Omega c$; since the inequality only gets weaker as $\gamma$ grows, this is equivalent to the book's $c_0 = \inf c$. "$b = 0$" means every $b_i$ vanishes a.e. in $\Omega$; $\|b_i\|_{L^\infty}$ is `eLpNorm (b i) ⊤` on $\Omega$. $C_1$ and $C_2$ are quantified before $c_0$ and before $u, v$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 103–104, Theorem 4.21

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_EllipticOperator

open MeasureTheory

namespace HunterPDE.Elliptic

/-- Theorem 4.21 of Hunter, *Notes on PDEs* (revised 6/18/2014), pp. 103–104 (energy estimates):
let `a` be the bilinear form (4.20) on `H¹₀(Ω)`, with coefficients satisfying (4.17) and the
uniform ellipticity condition (4.18) with constant `θ`. Then there are constants `C₁, C₂ > 0` and
`γ ∈ ℝ` such that for all `u, v ∈ H¹₀(Ω)`
  (4.23) `C₁ ‖u‖²_{H¹₀} ≤ a(u, u) + γ ‖u‖²_{L²}`,   (4.24) `|a(u, v)| ≤ C₂ ‖u‖_{H¹₀} ‖v‖_{H¹₀}`;
if `b = 0` one may take `γ = θ − c₀`, and if `b ≠ 0`, `γ = (1/2θ) ∑ᵢ ‖bᵢ‖²_{L^∞} + θ/2 − c₀`,
where `c₀ = inf_Ω c`.
Here `‖u‖_{H¹₀}` is the standard norm (4.13), `‖u‖²_{L²} = ∫_Ω u²`, `‖bᵢ‖_{L^∞(Ω)}` is the
essential supremum, and the explicit `γ` is asserted for every `c₀` with `c ≥ c₀` a.e. in `Ω`
(in particular for `c₀ = ess inf_Ω c`; a smaller `c₀` only enlarges `γ`). `b = 0` means every
`bᵢ` vanishes a.e. in `Ω`. -/
theorem energy_estimates {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (P : Coeffs n) (hP : P.Admissible Ω) (θ : ℝ) (hθ : P.UniformlyEllipticWith Ω θ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ u v : H10 n Ω, |form P u v| ≤ C₂ * ‖u‖ * ‖v‖) ∧
      ∀ c₀ : ℝ, (∀ᵐ x ∂(volume.restrict Ω), c₀ ≤ P.c x) →
        ((∀ i, P.b i =ᵐ[volume.restrict Ω] 0) →
          ∀ u : H10 n Ω, C₁ * ‖u‖ ^ 2 ≤ form P u u + (θ - c₀) * l2inner u u) ∧
        (¬ (∀ i, P.b i =ᵐ[volume.restrict Ω] 0) →
          ∀ u : H10 n Ω, C₁ * ‖u‖ ^ 2 ≤ form P u u +
            (1 / (2 * θ) * ∑ i, (eLpNorm (P.b i) ⊤ (volume.restrict Ω)).toReal ^ 2
              + θ / 2 - c₀) * l2inner u u) := by sorry

end HunterPDE.Elliptic
