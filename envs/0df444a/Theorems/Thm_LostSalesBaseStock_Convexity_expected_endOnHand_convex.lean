-- Prove2me | Theorems.Thm_LostSalesBaseStock_Convexity_expected_endOnHand_convex
-- name    : LostSalesBaseStock.Convexity.expected_endOnHand_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:10:14.566008+00:00
-- url     : https://prove2.me/theorems/7e5b86db-a612-40b1-8c94-2117cc87abe7
-- title:
--   Corollary 7 — in the Kaplan model, $\sum_{n=0}^m \beta_n E_\rho[i_n(S,\rho)]$ is convex in $S$
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space and $\rho = (\rho_n)_{n \ge 0}$ a sequence of independent, identically distributed, nonnegative integer-valued random variables, and let the arrival index follow the Kaplan model (Assumption 2): $\lambda_0(\rho) = 0$ and $\lambda_n(\rho) = \max(\lambda_{n-1}(\rho), n - \rho_n)$ for $n \ge 1$. Fix a realization of demands $D_0, \dots, D_N \ge 0$ and let $i_n(S, \rho)$ be the end-of-period inventory on hand of the order-up-to-$S$ lost-sales system driven by $\lambda(\rho)$. Then for every $m \in \{0, \dots, N\}$ and every nonnegative, weakly decreasing sequence $(\beta_n)$, the function
--
--   $$
--   S \mapsto \sum_{n=0}^{m} \beta_n \, E_\rho\big[i_n(S, \rho)\big]
--   $$
--
--   is convex on $S \in [0, \infty)$.
--
--   This is the convexity of the expected discounted storage-cost component, which the sample-path analysis cannot give; together with the first main result it yields convexity of the full expected discounted cost.
--
--   **Formalization Note** $E_\rho$ is the Bochner integral over $\Omega$ of the dynamics driven by the Kaplan index of $(\rho_k(\omega))_k$; the integrand is bounded for $S \ge 0$ and hence integrable. Measurability of each $\rho_n$ is stated as a hypothesis.
-- source:
--   Janakiraman and Roundy, Lost-Sales Problems with Stochastic Lead Times: Convexity Results for Base-Stock Policies, Oper. Res. 52(5) (2004), p. 800, Corollary 7 (with Assumption 2, p. 799)

import Mathlib
import Definitions.Def_LostSalesBaseStock_Convexity_kaplanIndex
import Definitions.Def_LostSalesBaseStock_Convexity_dynamics

open MeasureTheory ProbabilityTheory

namespace LostSalesBaseStock.Convexity

/-- Corollary 7 (Janakiraman–Roundy 2004, p. 800). Under Assumption 2 (the Kaplan lead-time
model: `λ_n = max(λ_{n−1}, n − ρ_n)`, `λ_0 = 0`, with `(ρ_n)` i.i.d. nonnegative
integer-valued random variables on a probability space `(Ω, P)`), for every fixed realization
of nonnegative demands `D_0, …, D_N`, every `m ∈ {0, …, N}` and every nonnegative, weakly
decreasing sequence `β`, the function `S ↦ ∑_{n=0}^{m} β_n E_ρ[i_n(S, ρ)]` is convex in
`S ∈ [0, ∞)`. Here `E_ρ` is the integral over `ω` of the dynamics driven by the Kaplan arrival
index of `ρ(ω)`. -/
theorem expected_endOnHand_convex {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ρ : ℕ → Ω → ℕ) (hρ_meas : ∀ n, Measurable (ρ n)) (hρ_indep : iIndepFun ρ P)
    (hρ_ident : ∀ n, IdentDistrib (ρ n) (ρ 0) P P)
    (N : ℕ) (D : ℕ → ℝ) (hD : ∀ n ≤ N, 0 ≤ D n)
    (β : ℕ → ℝ) (hβ_nonneg : ∀ n, 0 ≤ β n) (hβ_anti : Antitone β)
    (m : ℕ) (hm : m ≤ N) :
    ConvexOn ℝ (Set.Ici 0)
      (fun S : ℝ => ∑ n ∈ Finset.range (m + 1),
        β n * ∫ ω, endOnHand (kaplanIndex (fun k => ρ k ω)) D S n ∂P) := by sorry

end LostSalesBaseStock.Convexity
