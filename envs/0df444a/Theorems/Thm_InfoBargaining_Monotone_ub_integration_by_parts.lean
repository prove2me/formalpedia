-- Prove2me | Theorems.Thm_InfoBargaining_Monotone_ub_integration_by_parts
-- name    : InfoBargaining.Monotone.ub_integration_by_parts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:03.078578+00:00
-- url     : https://prove2.me/theorems/c1d46db5-02e4-4082-807b-bc35a446f1fa
-- title:
--   Proof of Proposition 1, p. 30 — integration by parts: U_b(α) = θ_b ∫_c^{v̄} [1 − G(v, α)] dv − k(α)
-- statement:
--   Let $G(v,\alpha)$ be the distribution function of the posterior mean, $k$ the information cost, and $U_b(\alpha)=\theta_b A(\alpha,c)-k(\alpha)$ the buyer's ex ante net surplus (6), with $\theta_b\in(0,1)$. For every $c\in\mathbb R$ and $\alpha\in(0,1)$, the function $v\mapsto 1-G(v,\alpha)$ is integrable on $(c,\infty)$ and
--   $$U_b(\alpha)=\theta_b\int_c^{\infty}\big[1-G(v,\alpha)\big]\,dv-k(\alpha).$$
--
--   This is the integration-by-parts form of the buyer's objective from which the proof of Proposition 1 reads off the cross effects of $\theta_b$ and $c$.
--
--   **Formalization Note** The paper's upper limit $\bar v$ is the top of the support of $v$, above which $1-G$ vanishes; with a prior of possibly unbounded support the integral is the Lebesgue integral over $(c,\infty)$, finite because the prior has a finite mean.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 30, Appendix, proof of Proposition 1, first sentence

import Mathlib
import Definitions.Def_InfoBargaining_Monotone_Setting

namespace InfoBargaining.Monotone

open MeasureTheory

/-- Proof of Proposition 1, p. 30, first sentence: by integration by parts,
`U_b(α) = θ_b ∫_c^{v̄} [1 - G(v, α)] dv - k(α)`; above the support `1 - G` vanishes, so the
integral is taken over `(c, ∞)`. -/
theorem ub_integration_by_parts (M : Model) {θb : ℝ} (hθb : θb ∈ Set.Ioo (0 : ℝ) 1)
    (c : ℝ) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    IntegrableOn (fun v => 1 - M.G v α) (Set.Ioi c) ∧
    M.Ub θb c α = θb * (∫ v in Set.Ioi c, (1 - M.G v α)) - M.k α := by sorry

end InfoBargaining.Monotone
