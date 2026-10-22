-- Prove2me | Theorems.Thm_JHolomorphic_enorm_le_of_hasWeakPartialsOn_ball
-- name    : JHolomorphic.enorm_le_of_hasWeakPartialsOn_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T15:56:16.722072+00:00
-- url     : https://prove2.me/theorems/7f5837e6-2dfe-4420-9632-e81f7a23c92d
-- title:
--   A sup bound for compactly supported $W^{1,p}$ maps on a disc, $p>2$
-- statement:
--   Let $p>2$ and let $E$ be a finite-dimensional real normed space. There is a constant $C$ with the following property. Let $c\in\mathbb{C}$, $\rho>0$, and let $\xi:\mathbb{C}\to E$ be continuous with $\operatorname{tsupport}\xi\subseteq B(c,\rho)$, whose weak partial derivatives $\xi_s,\xi_t$ on $B(c,\rho)$ lie in $L^p(B(c,\rho))$. Then for every $z\in\mathbb{C}$
--   $$|\xi(z)|\le C\,\rho^{1-2/p}\bigl(\|\xi_s\|_{L^p(B(c,\rho))}+\|\xi_t\|_{L^p(B(c,\rho))}\bigr).$$
--   This is the scale-invariant form of the embedding $W^{1,p}_0\subset L^\infty$ in two dimensions for $p>2$.
--
--   **Formalization Note** Weak partial derivatives are `HasWeakPartialsOn` on the open disc `ball c ρ`, tested against real $C^\infty$ functions with compact support in it; $\xi_s$ is the derivative in the direction $1$ and $\xi_t$ in the direction $i$. The left side is the extended norm `‖ξ z‖ₑ`; the norms on the right are `eLpNorm _ (ENNReal.ofReal p)` for the Lebesgue measure restricted to the disc, and the factor is `ENNReal.ofReal (C * ρ ^ (1 - 2 / p))`. The constant $C$ depends only on $p$ and $E$.
-- source:
--   Morrey's inequality; see L. C. Evans, Partial Differential Equations, §5.6.2, and D. Gilbarg, N. Trudinger, Elliptic PDE of Second Order, Theorem 7.10 and Theorem 7.17

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- Let `p > 2`. There is a constant `C` such that for every disc `B(c, ρ) ⊆ ℂ` and every
continuous `ξ : ℂ → E` with `tsupport ξ ⊆ B(c, ρ)` whose weak partials `ξₛ`, `ξₜ` on the disc lie in
`L^p(B(c, ρ))`, one has `‖ξ(z)‖ ≤ C ρ^{1-2/p} (‖ξₛ‖_{L^p} + ‖ξₜ‖_{L^p})` for every `z ∈ ℂ`. -/
theorem enorm_le_of_hasWeakPartialsOn_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → ∀ ξ ξs ξt : ℂ → E, Continuous ξ →
      tsupport ξ ⊆ ball c ρ → HasWeakPartialsOn (ball c ρ) ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict (ball c ρ)) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict (ball c ρ)) →
      ∀ z, ‖ξ z‖ₑ ≤ ENNReal.ofReal (C * ρ ^ (1 - 2 / p)) *
        (eLpNorm ξs (ENNReal.ofReal p) (volume.restrict (ball c ρ)) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict (ball c ρ))) := by
  sorry

end JHolomorphic
