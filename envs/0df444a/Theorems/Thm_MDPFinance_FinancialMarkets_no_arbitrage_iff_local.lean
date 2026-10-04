-- Prove2me | Theorems.Thm_MDPFinance_FinancialMarkets_no_arbitrage_iff_local
-- name    : MDPFinance.FinancialMarkets.no_arbitrage_iff_local
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:50:04.556972+00:00
-- url     : https://prove2.me/theorems/6c429be8-4a64-4150-a7aa-f5ea0f34470a
-- title:
--   Theorem 3.1.5 — no arbitrage iff local no-free-lunch (goal)
-- statement:
--   For an $N$-period financial market $M$: $M$ has no arbitrage opportunities if and only if,
--   for every $n = 0,\dots,N-1$ and every $\mathcal{F}_n$-measurable $\varphi_n \in
--   \mathbb{R}^d$,
--   $$
--   \varphi_n \cdot R_{n+1} \geq 0 \text{ a.s.} \implies \varphi_n \cdot R_{n+1} = 0 \text{ a.s.}
--   $$
--   This is the discrete-time, one-period-at-a-time characterization of no-arbitrage — a "no
--   free lunch locally implies no free lunch globally" equivalence — not the stronger existence
--   of an equivalent martingale measure, which this section does not prove.
--
--   **Formalization Note.** Part b) quantifies over *all* $\mathcal{F}_n$-measurable
--   $\varphi_n \in \mathbb{R}^d$, a one-period static condition on the relative return vector
--   $R_{n+1}$ alone — deliberately weaker machinery than a full self-financing strategy over the
--   whole horizon (Definition 3.1.4), which is exactly the content of the theorem: the global,
--   whole-horizon absence of arbitrage (`NoArbitrage`, quantifying over `Portfolio M`) reduces to
--   this simpler one-period condition.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 63, PDF 78, Theorem 3.1.5

import Mathlib
import Definitions.Def_MDPFinance_FinancialMarkets_DiscreteMarket
import Definitions.Def_MDPFinance_FinancialMarkets_Portfolio
import Definitions.Def_MDPFinance_FinancialMarkets_Arbitrage

open MeasureTheory ProbabilityTheory

namespace MDPFinance.FinancialMarkets

/-- Theorem 3.1.5 (Bäuerle–Rieder, p. 63, PDF 78) — the goal of this mission. Consider an
`N`-period financial market. The following two statements are equivalent: a) there are no
arbitrage opportunities; b) for `n = 0, …, N-1` and for all `Fam n`-measurable `φ_n ∈ ℝ^d` it
holds: `φ_n · R_{n+1} ≥ 0` `ℙ`-a.s. `⇒` `φ_n · R_{n+1} = 0` `ℙ`-a.s. -/
theorem no_arbitrage_iff_local {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : DiscreteFinancialMarket Ω d) :
    NoArbitrage M ↔
      ∀ n < M.N, ∀ φn : Ω → (Fin d → ℝ), (@Measurable Ω (Fin d → ℝ) (M.Fam n) _ φn) →
        (M.measIP {ω | 0 ≤ ∑ k, φn ω k * M.R (n + 1) ω k} = 1 →
          M.measIP {ω | ∑ k, φn ω k * M.R (n + 1) ω k = 0} = 1) := by sorry

end MDPFinance.FinancialMarkets
