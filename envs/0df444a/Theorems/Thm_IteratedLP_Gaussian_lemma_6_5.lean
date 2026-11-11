-- Prove2me | Theorems.Thm_IteratedLP_Gaussian_lemma_6_5
-- name    : IteratedLP.Gaussian.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:23:15.25519+00:00
-- url     : https://prove2.me/theorems/3aa25fc1-08ed-4caf-9219-cb57bee6d17c
-- title:
--   Lemma 6.5 — free-coordinate/active-row balance $q_t=\alpha P(U_t=\kappa_t)=\alpha P(\Lambda_t>0)$
-- statement:
--   Fix $\alpha>0$ and an input for round $t=p+1$ satisfying the assumptions of Section 6. Let $\omega^\star$ be a population optimizer (a maximizer of $\Psi_t$) with $V_t=\Psi_t(\omega^\star)>0$, let $(\tau_t,\eta_{x,t},\eta_{r,t})$ minimize the column dual at $\omega^\star$, let $\eta_{\lambda,t}$ be the row multiplier at $\omega^\star$, $\gamma_t=d_t(\omega^\star)/V_t$, and let $Y_t$, $U_t$, $\Lambda_t$ be the updates of Algorithm 2 (Steps 5–6). Then the updated free fraction $q_t=q\,\mathbb P(|Y_t|<1)$ satisfies
--   $$q_t=\alpha\,\mathbb P(U_t=\kappa_t)=\alpha\,\mathbb P(\Lambda_t>0).$$
--
--   The identity balances the coordinates that stay free against the rows that become tight; it is what makes the frozen fraction converge in Proposition 7.5.
--
--   Differences from the source:
--
--   - reading: at a population optimizer with V_t > 0, the updated free fraction → for every maximizer ω⋆ of Ψ_t with Ψ_t(ω⋆) > 0, every minimizer (τ, η_x, η_r) of the column dual at ω⋆ and every row multiplier η_λ at ω⋆, with q_t = q P(|Y_t| < 1) computed from them; reason: Algorithm 2's choices; quantifying over all of them is the full-strength reading
--   - encoding: P(|Y_t| < 1), P(U_t = κ_t), P(Λ_t > 0) → the measures of these events under colSpace S = π^col ⊗ N(0,1) ⊗ N(0,1) of (((X, R), G), V) and rowSpace S = π^row ⊗ N(0,1) of ((U, Λ), G_row), as reals; reason: the variables of Steps 5–6 realized on product spaces
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 29, Lemma 6.5

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_StateEvolution
import Definitions.Def_IteratedLP_Gaussian_StrictInput

open MeasureTheory ProbabilityTheory

namespace IteratedLP.Gaussian

/-- Lemma 6.5 (Free-coordinate/active-row balance, p. 29). Fix `α > 0` and an input for round
`t = p + 1` satisfying the assumptions of Section 6. Let `ω⋆` be a population optimizer
(a maximizer of `Ψ_t`) with `V_t = Ψ_t(ω⋆) > 0`, `(τ_t, η_{x,t}, η_{r,t})` a minimizer of the
column dual at `ω⋆`, `η_{λ,t}` a row multiplier at `ω⋆`, `γ_t = d_t(ω⋆)/V_t`, and
`Y_t`, `U_t`, `Λ_t` the updates of Algorithm 2 (Steps 5–6). Then the updated free fraction
`q_t = q P(|Y_t| < 1)` satisfies `q_t = α P(U_t = κ_t) = α P(Λ_t > 0)`. -/
theorem lemma_6_5 (α : ℝ) (hα : 0 < α) (p : ℕ) (κold : Fin p → ℝ) (κt : ℝ)
    (S : PopState p) (hS : IsSectionSixInput α κold κt S) (c : StepChoice p)
    (hmax : ∀ ω' : Param p, Psi α κt S ω' ≤ Psi α κt S c.ω) (hpos : 0 < Psi α κt S c.ω)
    (hcol : IsColDualMin S c.ω c.τ c.ηx c.ηr) (hrow : IsRowMultiplier α κt S c.ω c.ηl) :
    S.q * (colSpace S {w | |colUpdate (gammaAt α κt S c.ω) c.τ c.ηx c.ηr w| < 1}).toReal =
        α * (rowSpace S {w | rowUpdate α κt S c.ω c.ηl w.1 w.2 = κt}).toReal ∧
      α * (rowSpace S {w | rowUpdate α κt S c.ω c.ηl w.1 w.2 = κt}).toReal =
        α * (rowSpace S {w | 0 < rowMult α κt S c.ω c.ηl (valueAt α κt S c.ω) w}).toReal := by sorry

end IteratedLP.Gaussian
