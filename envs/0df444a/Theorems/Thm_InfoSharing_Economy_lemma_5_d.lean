-- Prove2me | Theorems.Thm_InfoSharing_Economy_lemma_5_d
-- name    : InfoSharing.Economy.lemma_5_d
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T00:00:14.387874+00:00
-- url     : https://prove2.me/theorems/af9a3e08-4b50-4ba0-8361-c6112d943038
-- title:
--   Lemma 5(d) — ordering of the retailer's ex ante profits $\pi_R(0)$, $\pi_R(1)$, $\pi_R(2)$ (production economy)
-- statement:
--   For every $\phi > 0$ there is a threshold $c_e^N \in (1/(1+\phi), 2/(1+\phi))$, depending only on $\phi$, such that the following holds. Let $0 < c_e < 2/(1+\phi)$, put $c = -c_e$, and let $a, b$ be reals. Let $(\theta, Y)$ satisfy the signal model with variance $\sigma^2$ and weight $\beta = \beta(t,\sigma)$, let $E$ be any family of pricing equilibria and write $\pi_R(n)$ for the retailer's entry of its payoff table at a profile with $n$ informed manufacturers. Then
--
--   $$\begin{aligned} &\pi_R(0) > \pi_R(1) > \pi_R(2) && \text{if } c_e < 1/(1+\phi),\\ &\pi_R(2) \ge \pi_R(1) \ge \pi_R(0) && \text{if } 1/(1+\phi) \le c_e \le c_e^N,\\ &\pi_R(1) > \pi_R(2) > \pi_R(0) && \text{if } c_e^N < c_e < 2/(1+\phi). \end{aligned}$$
--
--   This is the retailer's ranking of information-sharing outcomes when no payment is involved (Proposition 6).
--
--   **Formalization Note** The production economy model takes $c = -c_e$ with $0 < c_e < 2/(1+\phi)$ (the Assumption of p. 251). The ex ante profits are those of an equilibrium of the pricing game on the signal model, not the closed forms: the closed forms are the content of the §4.2 milestones. The production cost is the uncapped quadratic $bq - c_e q^2$ (the paper's cap at $\bar q = b/(2c_e)$ is assumed never to bind, footnote 11, p. 251). **Correction of the paper.** The single value $c_e^* = \frac{2+3\phi}{(1+2\phi)(1+\phi)}$ (which lies in $(1/(1+\phi), 2/(1+\phi))$) is excluded: there the slope $\phi(1+(1+\phi)c)/[(1+\phi)(2+(1+\phi)c)]$ of the best response (2) equals $-1$, so the pricing stage has a continuum of equilibria with different ex ante profits, and Lemma 1's uniqueness claim, on which the payoff table rests, fails.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 260, Lemma 5(d)

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_PayoffTable
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Economy

/-- **Lemma 5(d)** (Shang, Ha & Tong 2016, p. 260), production economy (`c = −c_e`) under the
Assumption `c_e < 2/(1+φ)`, stated on the payoff table of every family of pricing equilibria:
the ordering of the retailer's ex ante profits `π_R(0)`, `π_R(1)`, `π_R(2)` in the three
regions cut by `1/(1+φ)` and a threshold `c_e^N` that depends only on `φ`.

**Correction.** The value `c_e = (2+3φ)/((1+2φ)(1+φ))` is excluded: there the best-response
slope in (2) is `−1`, the pricing stage has a continuum of equilibria with different ex ante
profits, and Lemma 1's uniqueness (on which the paper's payoff table rests) fails. -/
theorem lemma_5_d :
    ∀ φ : ℝ, 0 < φ → ∃ cN : ℝ, 1 / (1 + φ) < cN ∧ cN < 2 / (1 + φ) ∧
    ∀ (ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ)
      (E : (Fin 2 → Status) → PricingProfile),
      c = -ce → 0 < ce → ce < 2 / (1 + φ) → ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)) →
      IsSignalModel μ θ Y σ β →
      IsPricingEqFamily μ θ Y a b c φ β E →
      ∀ i : Fin 2,
        let P := payoffTable μ θ Y a b c φ E
        (ce < 1 / (1 + φ) →
          P.R (onlyInformed i) < P.R (fun _ => Status.uninformed) ∧
          P.R (fun _ => Status.informed) < P.R (onlyInformed i)) ∧
        (1 / (1 + φ) ≤ ce → ce ≤ cN →
          P.R (onlyInformed i) ≤ P.R (fun _ => Status.informed) ∧
          P.R (fun _ => Status.uninformed) ≤ P.R (onlyInformed i)) ∧
        (cN < ce →
          P.R (fun _ => Status.informed) < P.R (onlyInformed i) ∧
          P.R (fun _ => Status.uninformed) < P.R (fun _ => Status.informed)) := by sorry

end InfoSharing.Economy
