-- Prove2me | Theorems.Thm_MarketMakerAds_Supplement_theorem_4
-- name    : MarketMakerAds.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:34:48.536488+00:00
-- url     : https://prove2.me/theorems/6aacd3f9-3202-449a-b4ce-8b9502588086
-- title:
--   Theorem 4 — heterogeneous risk aversion: price range and Pareto price $p^*_{M,k}$ (corrected: $\beta_k>0$, $E[\ell]>0$, $\mathrm{Cov}(\ell,c)\le0$; range closed only for atomless values)
-- statement:
--   Consider a market with heterogeneous risk aversion: $k$ populations with parameters $\theta_1\le\cdots\le\theta_k$ (all CARA with $\alpha_i>0$, or all mean-variance with $\beta_i\ge0$), random labelled unit values, $I$ units, and the no-contract clearing price $c$ with law $g$. A price $p$ is an **equilibrium Market-Maker price** if some clearing-price law $h$ is reproduced by the buyers' own choices under $h$, the Market-Maker does not default ($\ell\le I$ almost surely) and some unit buys the contract with positive probability. Let $p^*_{M,k}$ be eq. (3) for the most risk-averse population, applied to $g$, and $\ell$ the number of contract units at $p^*_{M,k}$.
--
--   **(a) Non-uniqueness.** For each family (CARA and mean-variance) there is a market with $k\ge2$ strictly ordered parameters, every population present with positive probability, and a clearing price with a density and a top of support $p_{\max}$, which has two distinct equilibrium Market-Maker prices.
--
--   For every market whose clearing price has top of support $p_{\max}$ ($c\le p_{\max}$ a.s., $\mathbb P(c>v)>0$ for $v<p_{\max}$) and no atom at $p_{\max}$:
--
--   **(b) A range of prices.** If $\mathbf E[\ell]>0$, the set $S$ of equilibrium prices satisfies, for some $q\le p^*_{M,k}$,
--   $$
--   (q,p^*_{M,k}]\subseteq S\subseteq[q,p^*_{M,k}],
--   $$
--   and $S=[q,p^*_{M,k}]$ when no unit value has an atom.
--
--   **(c) The Pareto price $p^*_{M,k}$.**
--   1. $g$ is an equilibrium law at $p^*_{M,k}$, and $p^*_{M,k}$ is an equilibrium price when $\mathbf E[\ell]>0$.
--   2. *Each buyer's utility stays the same:* a contract unit's utility equals its auction utility; the contract units are exactly the units of a population with $\theta_i=\theta_k$ and value $v\ge\max(p_{\max},p^*_{M,k})$; and the buyers' utility sum is unchanged in every outcome.
--   3. *Efficiency remains optimal:* almost surely $\ell\le I$, the clearing price and the allocated value are unchanged, and no $I$ units have a larger total value.
--   4. *Revenue strictly increases*, $\mathbf E[R_0]<\mathbf E[R_1]$, if $\beta_k>0$ (resp. $\alpha_k>0$), $\mathbf E[\ell]>0$ and $\mathbf E[\ell c]\le\mathbf E[\ell]\,\mathbf E[c]$.
--   5. *Welfare strictly increases*, $\mathbf E[W_0]<\mathbf E[W_1]$, under the hypotheses of 4 and integrability of the buyers' utility sum.
--
--   With $k=1$, part (c) is Theorem 3. Below $p^*_{M,k}$ the less risk-averse buyers start to buy the contract and the allocation may become inefficient (p.20).
--
--   **Formalization Note** Population labels are per unit and random, so the proportions $\rho_i$ are the law of the labels.
--
--   Differences from the source:
--   - correction: revenue and welfare strictly increase at p*_{M,k} for β_k ≥ 0 → assumes β_k > 0 (mean-variance); reason: with k = 1 this is Theorem 3, and Theorem 3's counterexample C1 applies (I = 1, values 2 and U[0,1], β = 0: p*_M = µ_A = 1/2 and E[R₁ − R₀] = 0)
--   - correction: unconditional strict increase, and a range of equilibrium prices with top p*_{M,k} → (b) and (c)(4)–(5) assume E[ℓ] > 0, also for p*_{M,k} to be an equilibrium price; reason: counterexample C3, also with k = 2 (I = 1, two i.i.d. U[0,1] units of population 1 with β₁ = 0, one unit of value 0 of population 2 with β₂ = 1: nobody buys at p*_{M,2}, E[R₁] = E[R₀], and p*_{M,2} is not an equilibrium price)
--   - correction: values not necessarily independent, strict revenue increase → assumes E[ℓc] ≤ E[ℓ]E[c]; reason: counterexample C2 with k = 1 (β = 1, scenarios {5, U[0.9,1]} and two U[0,0.1] values: E[R₁ − R₀] ≈ −0.124)
--   - encoding: welfare as an expectation → assumes the buyers' utility sum is integrable; reason: Lean's integral of a non-integrable function is 0
--   - generalization: populations with proportions ρ_i among the N buyers → random per-unit labels with an arbitrary joint law with the values; reason: fixed proportions are a special case
--   - generalization: clearing price v_{I+1} with a pdf g (p.10) → in (b) and (c), a clearing price with top of support p_max and no atom at p_max; reason: p_max is the paper's highest clearing price (Proposition 1, p.17), and a law with a density has no atom
--   - correction: the range of equilibrium prices is of the form [q, p*_{M,k}] (p.20) → (q, p*_{M,k}] ⊆ S ⊆ [q, p*_{M,k}] in general, and S = [q, p*_{M,k}] when no unit value has an atom; reason: the paper assumes a density for the clearing price, not for the unit values, and the lowest price can fail to be attained: I = 1, β = (0, 1), outcome A (prob. ½) units 10 (pop. 2), U[2.6, 3] (pop. 1), 2.5 (pop. 2), outcome B units 10 (pop. 2), U[1, 3] (pop. 1); the clearing price has a density, p*_{M,2} = 41/15, and S = (q, 41/15] with q = 2.5 − U_A(2.5) ≈ 2.4209 (at q the pop.-2 unit of value 2.5 is indifferent, buys and the Market-Maker defaults)
--   - generalization: α_1 < … < α_k in the proof (p.41) → θ_1 ≤ … ≤ θ_k; reason: the standing order of §6 (p.19) is non-strict
--   - reading: "the equilibrium Market-Maker price is not necessarily unique" → for each family some market with k ≥ 2 strictly ordered parameters, every population present and a clearing price with a density and a top of support has two distinct equilibrium prices; reason: "not necessarily" is an existence claim in the paper's model
--   - reading: "equilibrium Market-Maker price" → a fixed-point clearing-price law with no default a.s. and a contract buyer with positive probability; reason: the mutual best response of p.10, Remark 1 (p.16) and the feasibility notion of p.38
--   - reading: "a range … that depends on the range of risk parameters", "q the smallest price point where the Market-Maker contract does not default" → q is the lower end of S; reason: the dependence is the paper's gloss on q and p*_{M,k}, not a further claim
--   - encoding: CARA α_i ≥ 0 → α_i > 0; reason: eq. (3) divides by α
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Theorem 4, p.20 (with the range [q, p*_{M,k}], p.20); proof Appendix G, pp.40–41

import Mathlib
import Definitions.Def_MarketMakerAds_Supplement_HetMarket

open MeasureTheory

namespace MarketMakerAds

namespace Supplement

/-- **Theorem 4 (Heterogeneous Risk Aversion), p.20 (proof Appendix G, pp.40–41) (corrected: as
Theorem 3, `θ_k`-model positive, `E[ℓ] > 0`, `Cov(ℓ, c) ≤ 0`; range closed at `q` only for atomless unit values).**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Theorem 4, p.20:
"Under heterogeneous risk aversion, the equilibrium Market-Maker price is not necessarily unique.
Instead, there exists a range of equilibrium prices that depends on the range of risk parameters.
There always exists at least one price, p*_{M,k}, that strictly increases (i) the seller's revenue
and (ii) the welfare. In addition, each buyer's utility stays the same and the efficiency remains
optimal." With p.20: "The range of possible prices is of the form [q, p*_{M,k}], where q corresponds
to the smallest price point where the Market-Maker contract does not default."

In a heterogeneous market `H` (`HetMarket`: `k` populations with ordered parameters, random
labelled unit values), an **equilibrium price** `p` is one with a clearing-price law `h` that is the
law of the clearing price the buyers' own choices under `h` induce, with no default (`ℓ ≤ I` a.s.)
and some buyer for the contract with positive probability (`IsEqPrice`). Let `g` be the
no-contract clearing-price law and `p*_{M,k} = pStar (model k) g` (eq. (3) with `α_k`, resp.
`β_k`).
* **(a) not necessarily unique**: for each family (CARA and mean-variance) there is a market with
  `k ≥ 2` strictly ordered parameters, every population present with positive probability, and a
  clearing price with a density (the paper's `pdf g(·)`, p.10) and a top of support `p_max`, that
  has two distinct equilibrium prices.
* For every market whose clearing price `c` has top of support `p_max` (`c ≤ p_max` a.s.,
  `P(c > v) > 0` for `v < p_max`) without an atom at `p_max`:
  * **(b) a range**: if `E[ℓ] > 0` at `p*_{M,k}`, the set `S` of equilibrium prices satisfies
    `(q, p*_{M,k}] ⊆ S ⊆ [q, p*_{M,k}]` for some `q ≤ p*_{M,k}`, and `S = [q, p*_{M,k}]` when no
    unit value has an atom (the paper's setting, where values have a density);
  * **(c) the price `p*_{M,k}`**: `g` is an equilibrium law at `p*_{M,k}` (and `p*_{M,k}` an
    equilibrium price when `E[ℓ] > 0`); each contract unit's utility equals its auction utility;
    the contract units are exactly the units of a population with `θ_i = θ_k` and value
    `v ≥ max(p_max, p*_{M,k})`; the sum of the buyers' utilities is unchanged in every outcome;
    almost surely `ℓ ≤ I`, the clearing price and the allocated value are unchanged and optimal;
    and, if the model of population `k` is positive (`β_k > 0`, resp. `α_k > 0`), `E[ℓ] > 0` and
    `E[ℓ c] ≤ E[ℓ] E[c]`, the expected revenue strictly increases, and so does the expected welfare
    when the buyers' utility sum is integrable.

**Formalization Note** (c) carries the published corrections of Theorem 3 (`MarketMakerAds.theorem_3`,
which is (c) for `k = 1`): `β_k = 0` gives `p*_{M,k} = µ_A`; with `E[ℓ] = 0` nobody buys; correlated
values can make revenue fall. (b) corrects the printed closed range `[q, p*_{M,k}]`: with ties
going to the Market-Maker, the lowest non-defaulting price need not be attained when a unit value
has an atom (a unit indifferent at `q` buys and makes the Market-Maker default). The paper assumes a
density for the clearing price (p.10), not for the unit values: with `I = 1`, `β = (0, 1)`, outcome A
(prob. ½) units `10` (pop. 2), `U[2.6, 3]` (pop. 1), `2.5` (pop. 2), outcome B units `10` (pop. 2),
`U[1, 3]` (pop. 1), the clearing price has a density, `p*_{M,2} = 41/15` and the set of equilibrium
prices is `(q, 41/15]` with `q = 2.5 − U_A(2.5) ≈ 2.4209`. So the closed endpoint is claimed only for
atomless unit values. Labels are per unit and random, so the proportions `ρ_i` are the law of the
labels. -/
theorem theorem_4 :
    -- (a) the equilibrium Market-Maker price is not necessarily unique
    (∀ fam : RiskFamily, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (_ : IsProbabilityMeasure P) (H : HetMarket Ω),
      H.fam = fam ∧ 2 ≤ H.k ∧ StrictMono H.θ ∧
      (∀ i : Fin H.k, 0 < P {ω | ∃ j < H.N ω, H.T ω j = i}) ∧
      H.priceLaw P ≪ volume ∧
      (∃ pmax : ℝ, (∀ᵐ ω ∂P, H.c ω ≤ pmax) ∧ (∀ v < pmax, 0 < P {ω | v < H.c ω})) ∧
      ∃ p₁ p₂ : ℝ, p₁ ≠ p₂ ∧ H.IsEqPrice P p₁ ∧ H.IsEqPrice P p₂) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (H : HetMarket Ω) (pmax : ℝ),
      (∀ᵐ ω ∂P, H.c ω ≤ pmax) → (∀ v < pmax, 0 < P {ω | v < H.c ω}) →
      P {ω | H.c ω = pmax} = 0 →
      -- (b) a range of equilibrium prices with top p*_{M,k}
      (0 < ∫ ω, (H.nMM (H.priceLaw P) (H.pStarK P) ω : ℝ) ∂P →
        ∃ q ≤ H.pStarK P, Set.Ioc q (H.pStarK P) ⊆ {p | H.IsEqPrice P p} ∧
          {p | H.IsEqPrice P p} ⊆ Set.Icc q (H.pStarK P) ∧
          ((∀ (j : ℕ) (x : ℝ), P {ω | j < H.N ω ∧ H.V ω j = x} = 0) → H.IsEqPrice P q)) ∧
      -- (c) the Pareto price p*_{M,k}
      (H.IsEqLaw P (H.priceLaw P) (H.pStarK P) ∧
        (0 < ∫ ω, (H.nMM (H.priceLaw P) (H.pStarK P) ω : ℝ) ∂P → H.IsEqPrice P (H.pStarK P)) ∧
        -- each buyer's utility stays the same
        (∀ (i : Fin H.k) (v : ℝ), H.buys (H.priceLaw P) (H.pStarK P) (v, i) →
          Ubuy (H.model i) v (H.pStarK P) = UA (H.model i) (H.priceLaw P) v) ∧
        (∀ (i : Fin H.k) (v : ℝ), H.buys (H.priceLaw P) (H.pStarK P) (v, i) ↔
          (H.θ i = H.θ H.last ∧ max pmax (H.pStarK P) ≤ v)) ∧
        (∀ ω, H.util1 (H.priceLaw P) (H.pStarK P) ω = H.util0 P ω) ∧
        -- the efficiency remains optimal
        (∀ᵐ ω ∂P, H.nMM (H.priceLaw P) (H.pStarK P) ω ≤ H.I ∧
          H.c1 (H.priceLaw P) (H.pStarK P) ω = H.c ω ∧
          H.eff1 (H.priceLaw P) (H.pStarK P) ω = H.eff0 ω ∧
          ∀ s : List ℝ, s.Sublist (H.units ω) → s.length ≤ H.I → s.sum ≤ H.eff0 ω) ∧
        -- (i) the seller's revenue strictly increases
        ((H.model H.last).IsPositive →
          0 < ∫ ω, (H.nMM (H.priceLaw P) (H.pStarK P) ω : ℝ) ∂P →
          ∫ ω, (H.nMM (H.priceLaw P) (H.pStarK P) ω : ℝ) * H.c ω ∂P ≤
            (∫ ω, (H.nMM (H.priceLaw P) (H.pStarK P) ω : ℝ) ∂P) * ∫ ω, H.c ω ∂P →
          ∫ ω, H.rev0 ω ∂P < ∫ ω, H.rev1 (H.priceLaw P) (H.pStarK P) ω ∂P) ∧
        -- (ii) the welfare strictly increases
        ((H.model H.last).IsPositive →
          0 < ∫ ω, (H.nMM (H.priceLaw P) (H.pStarK P) ω : ℝ) ∂P →
          ∫ ω, (H.nMM (H.priceLaw P) (H.pStarK P) ω : ℝ) * H.c ω ∂P ≤
            (∫ ω, (H.nMM (H.priceLaw P) (H.pStarK P) ω : ℝ) ∂P) * ∫ ω, H.c ω ∂P →
          Integrable (H.util0 P) P →
          ∫ ω, H.welfare0 P ω ∂P < ∫ ω, H.welfare1 (H.priceLaw P) (H.pStarK P) ω ∂P))) := by sorry

end Supplement

end MarketMakerAds
