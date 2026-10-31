-- Prove2me | Theorems.Thm_MarketMakerAds_theorem_3
-- name    : MarketMakerAds.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:25.475777+00:00
-- url     : https://prove2.me/theorems/e453c34e-9364-4884-80ff-26a87d7c73d0
-- title:
--   Theorem 3 (Market-Maker Pareto Improvement) (corrected: $\beta>0$, $\mathrm{Cov}(\ell,c)\le0$, $\mathbf E[\ell]>0$)
-- statement:
--   A seller sells $I$ identical units. On a probability space $(\Omega,\mathbb P)$ the market outcome is a random list of nonnegative unit values: a random number of units demanded, with values that may be correlated, and a buyer of demand $k$ counted as $k$ units. Without the contract, the $I$ highest units win the $(I+1)$-th price auction and pay the clearing price $c$, the $(I+1)$-th highest unit value. Every buyer evaluates the auction with the law $g$ of $c$. The seller offers the Market-Maker contract at
--
--   $$
--   p=p^*_M=\begin{cases}\mu_A+\beta\sigma_A^2,\\ \tfrac1\alpha\log\mathbf E[e^{\alpha c}],\end{cases}
--   $$
--
--   computed from $g$, with $\beta\ge0$ (mean-variance), resp. $\alpha>0$ (CARA). A unit of value $v$ buys the contract if $p\le v$ and $U_A(v)\le U_{\mathrm{buy}}(v,p)$ (ties to the contract). The other units go to the $(I-\ell+1)$-th price auction for the remaining units, where $\ell$ is the number of contract units. Let $p_{\max}$ be the top of the support of $c$ with no atom there: $c\le p_{\max}$ almost surely, $\mathbb P(c>v)>0$ for every $v<p_{\max}$, and $\mathbb P(c=p_{\max})=0$. Then:
--
--   1. **Each buyer's utility remains the same.** A unit that buys the contract gets $U_{\mathrm{buy}}(v,p)=U_A(v)$. The buyers are exactly the units with $v\ge\max(p_{\max},p)$. In every outcome the sum of the buyers' utilities with the contract equals the sum without it.
--   2. **Efficiency remains optimal.** Almost surely, $\ell\le I$, the auction clearing price with the contract equals $c$, and the allocated value with the contract equals the sum $\mathrm{Eff}_0$ of the $I$ highest unit values. No choice of at most $I$ units has a larger total value than $\mathrm{Eff}_0$.
--   3. **Revenue strictly increases.** If $\beta>0$ (resp. $\alpha>0$), $\mathbf E[\ell]>0$ and $\mathbf E[\ell\,c]\le\mathbf E[\ell]\,\mathbf E[c]$, then $\mathbf E[R_0]<\mathbf E[R_1]$.
--   4. **Welfare strictly increases.** Under the hypotheses of 3, if the buyers' utility sum without the contract is integrable, then $\mathbf E[W_0]<\mathbf E[W_1]$, where welfare is the buyers' utilities plus the revenue.
--
--   Here $R_0=Ic$ and $R_1=\ell p+(I-\ell)c_1$, with $c_1$ the clearing price of the second-stage auction, are computed from the two outcomes.
--
--   Offering the contract at $p^*_M$ is thus a Pareto improvement: buyers keep their utility, the allocation stays efficient, and the seller gains the markup on every contract unit.
--
--   Differences from the source:
--   - correction: $\beta\ge0$ → $\beta>0$ for the strict revenue and welfare clauses; reason: at $\beta=0$, $p^*_M=\mu_A$; with $I=1$, one buyer of value $2$ and one of value $U\sim U[0,1]$, $\ell=1$ and $\mathbf E[R_1-R_0]=\mathbf E[1/2-U]=0$.
--   - correction: no hypothesis on the joint law of $\ell$ and $c$ → $\mathbf E[\ell c]\le\mathbf E[\ell]\mathbf E[c]$; reason: the model allows correlated values and a random number of buyers; with $I=1$, $\beta=1$, and two equally likely scenarios (values $\{5,U\}$, $U\sim U[0.9,1]$, or two i.i.d. $U[0,0.1]$ values), $g$ has a density, $p_{\max}=1$, $p^*_M\approx0.702$ and $\mathbf E[R_1-R_0]=\tfrac12(p^*_M-0.95)\approx-0.124<0$. Independence of $\ell$ and $c$ is a special case.
--   - correction: no hypothesis on $\ell$ → $\mathbf E[\ell]>0$; reason: with $I=1$ and two buyers with i.i.d. $U[0,1]$ values, $p_{\max}=1$ and $\ell=0$ almost surely, so revenue is unchanged.
--   - generalization: the clearing price has a density $g$ → only no atom at $p_{\max}$, the top of the support of $c$; reason: a density has no atoms; without this, more than $I$ buyers can choose the contract (Remark 1).
--   - reading: a buyer "opts for" the contract → $p\le v$ and $U_A(v)\le U_{\mathrm{buy}}(v,p)$, ties to the contract, every other buyer receives $U_A(v)$ even when negative; reason: p.10 (utility comparison), p.18 (indifferent buyers opt for the contract), eq. (2) (no purchase below $p_M$), and Step 1 of p.11 (the clearing price is the $(I+1)$-th value of all buyers); p.14's remark that an agent with negative utility does not participate is not built in, and it would not change any buyer's utility, since contract buyers have $U_{\mathrm{buy}}=U_A\ge0$ there.
--   - reading: the market → a random list of nonnegative unit values, $c$ its $(I+1)$-th highest entry ($0$ if at most $I$ units are demanded), $R_0=Ic$; reason: Assumption 2 (p.11) puts everything on a per-unit basis; values are nonnegative because the paper's clearing prices live on $[0,\infty)$ (pp.30–31).
--   - reading: the market with the contract → contract units first, then the $(I-\ell+1)$-th price auction on the other units; efficiency = allocated value, "optimal" = no $I$ units have a larger total, welfare = buyers' utilities plus revenue; reason: proof of Theorem 3 (pp.18–19) and §3.4 (p.13).
--   - encoding: $\alpha\ge0$ → $\alpha>0$; reason: $p^*_M$ is undefined at $\alpha=0$.
--   - encoding: welfare compared in expectation → the buyers' utility sum without the contract is integrable; reason: the welfare comparison is between finite expectations.
--   - encoding: $I-\ell$ → natural-number subtraction cast to $\mathbb R$; reason: the theorem proves $\ell\le I$ almost surely, where it is the real difference.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Theorem 3, p.18 (proof pp.18–19)

import Mathlib
import Definitions.Def_MarketMakerAds_Market

open MeasureTheory

namespace MarketMakerAds

/-- **Theorem 3 (Market-Maker Pareto Improvement), p.18 (corrected: β > 0, Cov(ℓ, c) ≤ 0,
E[ℓ] > 0).**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Theorem 3, p.18
(proof pp.18–19): "When offering the Market-Maker contract at price p*_M, both the seller's revenue
and the welfare strictly increase. Moreover, the efficiency remains optimal and each buyer's
utility remains the same."

The seller sells `I` units; the market outcome `ω` is a random list of nonnegative unit values
(`Market`), `c` is the `(I+1)`-th highest unit value with law `g`, and every buyer evaluates the
auction with `g`. The contract is offered at `p = p*_M = pStar m g`. Assume `β ≥ 0`, resp. `α > 0`,
and that `p_max` is the top of the support of `c` (`c ≤ p_max` a.s., `P(c > v) > 0` for all
`v < p_max`) with no atom at `p_max`. Then:
1. **each buyer's utility remains the same**: a unit that buys the contract gets
   `U_buy(v, p) = U_A(v)`, the buyers are exactly those with `v ≥ max(p_max, p)`, and the sum of the
   buyers' utilities is unchanged in every outcome;
2. **efficiency remains optimal**, almost surely: at most `I` units buy the contract, the auction
   clearing price is unchanged, the allocated value is unchanged, and no `I` units have a larger
   total value;
3. **revenue strictly increases**, `E[R₀] < E[R₁]`, if `β > 0` (resp. `α > 0`), `E[ℓ] > 0` and
   `E[ℓ c] ≤ E[ℓ] E[c]`, where `ℓ` is the number of contract units;
4. **welfare strictly increases**, `E[W₀] < E[W₁]`, under the hypotheses of 3 and integrability of
   the buyers' utility sum.

**Formalization Note** Corrections: with `β = 0`, `p*_M = µ_A` and revenue does not strictly
increase; with `E[ℓ] = 0` nobody buys; with `ℓ` positively correlated with `c` revenue can fall
(the model allows correlated values and a random number of buyers). Independence of `ℓ` and `c` is
a special case of `E[ℓ c] ≤ E[ℓ] E[c]`. The paper's density for `c` is replaced by "no atom at
`p_max`". -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Market Ω) (m : RiskModel) (hm : m.IsAdmissible) (pmax : ℝ)
    (h_le : ∀ᵐ ω ∂P, M.c ω ≤ pmax) (h_top : ∀ v < pmax, 0 < P {ω | v < M.c ω})
    (h_atom : P {ω | M.c ω = pmax} = 0) :
    -- 1. each buyer's utility remains the same
    ((∀ v : ℝ, buysMM m (M.priceLaw P) (M.mmPrice m P) v →
        Ubuy m v (M.mmPrice m P) = UA m (M.priceLaw P) v) ∧
      (∀ v : ℝ, buysMM m (M.priceLaw P) (M.mmPrice m P) v ↔ max pmax (M.mmPrice m P) ≤ v) ∧
      (∀ ω, M.util1 m P ω = M.util0 m P ω)) ∧
    -- 2. efficiency remains optimal
    (∀ᵐ ω ∂P, M.nMM m P ω ≤ M.I ∧ M.c1 m P ω = M.c ω ∧ M.eff1 m P ω = M.eff0 ω ∧
      ∀ s : List ℝ, s.Sublist (M.units ω) → s.length ≤ M.I → s.sum ≤ M.eff0 ω) ∧
    -- 3. revenue strictly increases
    (m.IsPositive → 0 < ∫ ω, (M.nMM m P ω : ℝ) ∂P →
      ∫ ω, (M.nMM m P ω : ℝ) * M.c ω ∂P ≤ (∫ ω, (M.nMM m P ω : ℝ) ∂P) * ∫ ω, M.c ω ∂P →
      ∫ ω, M.rev0 ω ∂P < ∫ ω, M.rev1 m P ω ∂P) ∧
    -- 4. welfare strictly increases
    (m.IsPositive → 0 < ∫ ω, (M.nMM m P ω : ℝ) ∂P →
      ∫ ω, (M.nMM m P ω : ℝ) * M.c ω ∂P ≤ (∫ ω, (M.nMM m P ω : ℝ) ∂P) * ∫ ω, M.c ω ∂P →
      Integrable (M.util0 m P) P →
      ∫ ω, M.welfare0 m P ω ∂P < ∫ ω, M.welfare1 m P ω ∂P) := by sorry

end MarketMakerAds
