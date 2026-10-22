-- Prove2me | Theorems.Thm_LostSalesBaseStock_Convexity_expected_onHand_convex
-- name    : LostSalesBaseStock.Convexity.expected_onHand_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:59:15.902032+00:00
-- url     : https://prove2.me/theorems/c1692b13-73f3-467f-99fd-0351b340f004
-- title:
--   Lemma 6 — in the Kaplan model, $\sum_{n=0}^m \beta_n E_\rho[x_n(S,\rho)]$ is convex in $S$
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space and $\rho = (\rho_n)_{n \ge 0}$ a sequence of independent, identically distributed, nonnegative integer-valued random variables. Under Assumption 2 (the Kaplan lead-time model), the arrival index is $\lambda_0(\rho) = 0$ and $\lambda_n(\rho) = \max(\lambda_{n-1}(\rho), n - \rho_n)$ for $n \ge 1$. Fix a realization of demands $D_0, \dots, D_N \ge 0$ and let $x_n(S, \rho)$ be the inventory on hand after receipts in period $n$ of the order-up-to-$S$ lost-sales system driven by $\lambda(\rho)$. Then for every $m \in \{0, \dots, N\}$ and every nonnegative, weakly decreasing sequence $(\beta_n)$, the function
--
--   $$
--   S \mapsto \sum_{n=0}^{m} \beta_n \, E_\rho\big[x_n(S, \rho)\big]
--   $$
--
--   is convex on $S \in [0, \infty)$, where $E_\rho$ is the expectation with respect to the random vector $\rho$.
--
--   On a single sample path this sum need not be convex; the lemma is where the Kaplan structure of the lead times enters.
--
--   **Formalization Note** $E_\rho[x_n(S,\rho)]$ is the Bochner integral over $\omega \in \Omega$ of $x_n$ computed with the arrival index of $(\rho_k(\omega))_k$. For $S \ge 0$ the integrand is bounded ($0 \le x_n \le S$) and depends on finitely many $\rho_k$, so it is integrable. Measurability of each $\rho_n$ is the standing convention of the field and is stated as a hypothesis; independence is `iIndepFun` and identical distribution is `IdentDistrib (ρ n) (ρ 0)` for every $n$.
-- source:
--   Janakiraman and Roundy, Lost-Sales Problems with Stochastic Lead Times: Convexity Results for Base-Stock Policies, Oper. Res. 52(5) (2004), p. 800, Lemma 6 (with Assumption 2, p. 799)

import Mathlib
import Definitions.Def_LostSalesBaseStock_Convexity_kaplanIndex
import Definitions.Def_LostSalesBaseStock_Convexity_dynamics

open MeasureTheory ProbabilityTheory

namespace LostSalesBaseStock.Convexity

/-- Lemma 6 (Janakiraman–Roundy 2004, p. 800). Under Assumption 2 (the Kaplan lead-time
model: `λ_n = max(λ_{n−1}, n − ρ_n)`, `λ_0 = 0`, with `(ρ_n)` i.i.d. nonnegative
integer-valued random variables on a probability space `(Ω, P)`), for every fixed realization
of nonnegative demands `D_0, …, D_N`, every `m ∈ {0, …, N}` and every nonnegative, weakly
decreasing sequence `β`, the function `S ↦ ∑_{n=0}^{m} β_n E_ρ[x_n(S, ρ)]` is convex in
`S ∈ [0, ∞)`. Here `E_ρ` is the integral over `ω` of the dynamics driven by the Kaplan arrival
index of `ρ(ω)`. -/
theorem expected_onHand_convex {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ρ : ℕ → Ω → ℕ) (hρ_meas : ∀ n, Measurable (ρ n)) (hρ_indep : iIndepFun ρ P)
    (hρ_ident : ∀ n, IdentDistrib (ρ n) (ρ 0) P P)
    (N : ℕ) (D : ℕ → ℝ) (hD : ∀ n ≤ N, 0 ≤ D n)
    (β : ℕ → ℝ) (hβ_nonneg : ∀ n, 0 ≤ β n) (hβ_anti : Antitone β)
    (m : ℕ) (hm : m ≤ N) :
    ConvexOn ℝ (Set.Ici 0)
      (fun S : ℝ => ∑ n ∈ Finset.range (m + 1),
        β n * ∫ ω, onHand (kaplanIndex (fun k => ρ k ω)) D S n ∂P) := by sorry

end LostSalesBaseStock.Convexity
