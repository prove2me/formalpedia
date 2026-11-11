-- Prove2me | Theorems.Thm_IteratedLP_Gaussian_proposition_6_6
-- name    : IteratedLP.Gaussian.proposition_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:23:14.98262+00:00
-- url     : https://prove2.me/theorems/65962bee-ef03-448f-b6e6-d93d1b4b2c53
-- title:
--   Proposition 6.6 — uniqueness of the positive population optimizer $\omega^\star_t$
-- statement:
--   Fix $\alpha>0$ and an input for round $t=p+1$ satisfying the assumptions of Section 6, with population objective $\Psi_t$ of (6.17). Assume $V_t:=\max_\omega\Psi_t(\omega)>0$, and suppose that at every maximizing parameter the column and row dual optima are attained at finite multipliers, with positive column second-moment multiplier: some $(\tau,\eta_x,\eta_r)$ with $\tau>0$ minimizes the column dual (6.12), and some $\eta_\lambda$ represents the row projection as in (6.14). Then
--   $$\operatorname*{arg\,max}_\omega\Psi_t(\omega)=\{\omega^\star_t\}$$
--   is a single point.
--
--   Uniqueness of $\omega^\star_t$ is what lets Algorithm 2 speak of "the maximizer" and what the localization of the finite LP optimizer converges to.
--
--   Differences from the source:
--
--   - reading: Assume V_t := max_ω Ψ_t(ω) > 0 → hypotheses: some ω attains ⨆ Ψ_t, and ⨆ Ψ_t > 0; reason: the notation max presupposes that the maximum is attained
--   - reading: the column and row dual optima are attained at finite multipliers, with positive column second-moment multiplier → at every maximizer ω: some (τ, η_x, η_r) with τ > 0 minimizes colDual at ω, and some η_λ satisfies the row moment equation (6.14) for U = max{κ_t, Z_ω − η_λ⊤Λ}; reason: this is what attainment of the two duals means
--   - encoding: argmax_ω Ψ_t(ω) = {ω⋆_t} → ∃ ω⋆, {ω | Psi ω = ⨆ Psi} = {ω⋆}; reason: same statement
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 30, Proposition 6.6

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_StateEvolution
import Definitions.Def_IteratedLP_Gaussian_StrictInput

open MeasureTheory ProbabilityTheory

namespace IteratedLP.Gaussian

/-- Proposition 6.6 (Uniqueness of the positive population optimizer, p. 30). Fix `α > 0` and an
input for round `t = p + 1` satisfying the assumptions of Section 6. Assume
`V_t := max_ω Ψ_t(ω) > 0` (the maximum is attained and positive), and that at every maximizing
parameter the column dual (6.12) is minimized at finite multipliers `(τ, η_x, η_r)` with `τ > 0`
and the row dual is attained at a finite multiplier `η_λ` (eq. (6.14)). Then
`argmax_ω Ψ_t(ω) = {ω⋆_t}` is a single point. -/
theorem proposition_6_6 (α : ℝ) (hα : 0 < α) (p : ℕ) (κold : Fin p → ℝ) (κt : ℝ)
    (S : PopState p) (hS : IsSectionSixInput α κold κt S)
    (hmax : ∃ ω : Param p, Psi α κt S ω = ⨆ ω' : Param p, Psi α κt S ω')
    (hpos : 0 < ⨆ ω : Param p, Psi α κt S ω)
    (hdual : ∀ ω : Param p, Psi α κt S ω = ⨆ ω' : Param p, Psi α κt S ω' →
      (∃ (τ : ℝ) (ηx ηr : Fin p → ℝ), 0 < τ ∧ IsColDualMin S ω τ ηx ηr) ∧
      ∃ ηl : Fin p → ℝ, IsRowMultiplier α κt S ω ηl) :
    ∃ ωstar : Param p, {ω : Param p | Psi α κt S ω = ⨆ ω' : Param p, Psi α κt S ω'} = {ωstar} := by sorry

end IteratedLP.Gaussian
