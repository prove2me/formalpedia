-- Prove2me | Theorems.Thm_LeblSCV_Holomorphic_cauchy_derivative_formula_and_estimates
-- name    : LeblSCV.Holomorphic.cauchy_derivative_formula_and_estimates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:04:41.613178+00:00
-- url     : https://prove2.me/theorems/65893fdd-f3d3-46a2-a2b6-7cdab8c94c83
-- title:
--   Proposition 1.2.2 — Cauchy formula for derivatives, coefficients, Cauchy estimates
-- statement:
--   Let $\Delta = \Delta_\rho(a) \subset \mathbb{C}^n$ be a polydisc (all $\rho_k > 0$) with distinguished boundary $\Gamma$, and let $f : \overline{\Delta} \to \mathbb{C}$ be continuous and holomorphic in $\Delta$. Then:
--
--   1. for $z \in \Delta$ and every multi-index $\alpha \in \mathbb{N}_0^n$,
--   $$\frac{\partial^{|\alpha|} f}{\partial z^\alpha}(z) = \frac{1}{(2\pi i)^n} \int_\Gamma \frac{\alpha!\, f(\zeta)}{(\zeta - z)^{\alpha + 1}}\, d\zeta;$$
--   2. if $f$ is given on $\Delta$ by a power series $f(z) = \sum_\alpha c_\alpha (z-a)^\alpha$ converging uniformly absolutely on compact subsets of $\Delta$ (expansion (1.3)), then
--   $$c_\alpha = \frac{1}{\alpha!} \frac{\partial^{|\alpha|} f}{\partial z^\alpha}(a),$$
--   and the **Cauchy estimates** $|c_\alpha| \le \|f\|_\Gamma / \rho^\alpha$ hold.
--
--   Here $\alpha! = \alpha_1! \cdots \alpha_n!$, $\rho^\alpha = \rho_1^{\alpha_1} \cdots \rho_n^{\alpha_n}$, $(\zeta - z)^{\alpha+1} = \prod_k (\zeta_k - z_k)^{\alpha_k + 1}$, $d\zeta = d\zeta_1 \wedge \cdots \wedge d\zeta_n$, and $\|f\|_\Gamma = \sup_{\zeta \in \Gamma} |f(\zeta)|$. In particular the coefficients depend only on the derivatives of $f$ at $a$.
--
--   **Formalization Note.** $\partial^{|\alpha|}/\partial z^\alpha$ is the iterated Wirtinger derivative `wirtingerIter`; the integral over $\Gamma$ is `torusIntegral` (see Theorem 1.1.4). The Cauchy estimate is stated for every real $M$ with $|f| \le M$ on $\Gamma$: $|c_\alpha| \le M/\rho^\alpha$; taking $M = \|f\|_\Gamma$ (finite, as $f$ is continuous on the compact set $\Gamma$) gives the book's form, and the book's form implies this one. Expansion (1.3) is restated as hypotheses: uniform absolute convergence on every compact $K \subset \Delta$, and `HasSum` of the terms to $f(z)$ at every $z \in \Delta$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 22, Proposition 1.2.2

import Mathlib
import Definitions.Def_LeblSCV_Shared_polydisc
import Definitions.Def_LeblSCV_Holomorphic_distinguishedBoundary
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn
import Definitions.Def_LeblSCV_Holomorphic_wirtingerIter
import Definitions.Def_LeblSCV_Holomorphic_powerSeriesTerm

open Complex

namespace LeblSCV.Holomorphic

/-- Proposition 1.2.2 (Lebl, p. 22). Let `Δ = Δ_ρ(a)` be a polydisc with distinguished boundary `Γ`,
and `f` continuous on `closure Δ` and holomorphic in `Δ`. Then:
(1) for `z ∈ Δ` and every `α ∈ ℕ₀ⁿ`,
`∂^{|α|} f / ∂z^α (z) = (2πi)^{-n} ∫_Γ α! f(ζ) / (ζ - z)^{α + 1} dζ`;
(2) if `f(z) = ∑_α c_α (z - a)^α` on `Δ` with uniform absolute convergence on compact subsets
of `Δ` (expansion (1.3)), then `c_α = (1/α!) ∂^{|α|} f / ∂z^α (a)`, and the Cauchy estimates
`|c_α| ≤ ‖f‖_Γ / ρ^α` hold, stated here for every bound `M` of `|f|` on `Γ` (the least such
`M` being `‖f‖_Γ = sup_Γ |f|`). Here `α! = α_1! ⋯ α_n!`, `ρ^α = ρ_1^{α_1} ⋯ ρ_n^{α_n}`,
`(ζ - z)^{α+1} = ∏_k (ζ_k - z_k)^{α_k + 1}`. -/
theorem cauchy_derivative_formula_and_estimates {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ)
    (hρ : ∀ k, 0 < ρ k) {f : (Fin n → ℂ) → ℂ}
    (hcont : ContinuousOn f (closure (LeblSCV.Shared.polydisc a ρ)))
    (hf : IsHolomorphicOn f (LeblSCV.Shared.polydisc a ρ)) :
    (∀ z ∈ LeblSCV.Shared.polydisc a ρ, ∀ α : Fin n → ℕ,
      wirtingerIter α f z = ((2 * Real.pi * I) ^ n)⁻¹ *
        torusIntegral (fun ζ => ((∏ k : Fin n, (α k).factorial : ℕ) : ℂ) * f ζ /
          ∏ k : Fin n, (ζ k - z k) ^ (α k + 1)) a ρ) ∧
    (∀ c : (Fin n → ℕ) → ℂ,
      (∀ K ⊆ LeblSCV.Shared.polydisc a ρ, IsCompact K → ConvergesUniformlyAbsolutelyOn c a K) →
      (∀ z ∈ LeblSCV.Shared.polydisc a ρ, HasSum (fun α => powerSeriesTerm c a α z) (f z)) →
      (∀ α : Fin n → ℕ,
        c α = (((∏ k : Fin n, (α k).factorial : ℕ) : ℂ))⁻¹ * wirtingerIter α f a) ∧
      (∀ M : ℝ, (∀ ζ ∈ distinguishedBoundary a ρ, ‖f ζ‖ ≤ M) →
        ∀ α : Fin n → ℕ, ‖c α‖ ≤ M / ∏ k : Fin n, ρ k ^ α k)) := by sorry

end LeblSCV.Holomorphic
