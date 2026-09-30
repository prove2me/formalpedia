-- Prove2me | Theorems.Thm_InfoSharing_Economy_lemma_5_abc
-- name    : InfoSharing.Economy.lemma_5_abc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T23:55:38.294107+00:00
-- url     : https://prove2.me/theorems/e9601517-7bcb-4848-9c55-1b05fc179cd3
-- title:
--   Lemma 5(a)–(c) — comparisons of the manufacturers' ex ante profits (production economy)
-- statement:
--   For every $\phi > 0$ there is a threshold $c_e^a \in (1/(1+\phi), 2/(1+\phi))$, depending only on $\phi$, such that the following holds. Let $0 < c_e < 2/(1+\phi)$, put $c = -c_e$, and let $a, b$ be reals. Let $(\theta, Y)$ satisfy the signal model with variance $\sigma^2$ and weight $\beta = \beta(t,\sigma)$, let $E$ be any family of pricing equilibria and write $\pi_M(0)$, $\pi_M^U(1)$, $\pi_M^I(1)$, $\pi_M(2)$ for manufacturer $i$'s entries of its payoff table (nobody informed; only the rival informed; only $i$ informed; both informed). Then
--
--   1. (a) $\pi_M^I(1) \ge \pi_M(0)$; and $\pi_M(2) \ge \pi_M^U(1)$ if $c_e \le c_e^a$, $\pi_M(2) < \pi_M^U(1)$ otherwise;
--   2. (b) $\pi_M(0) \ge \pi_M^U(1)$ if $\frac{1}{1+\phi} \le c_e \le \frac{4+5\phi}{(2+3\phi)(1+\phi)}$, and $\pi_M(0) < \pi_M^U(1)$ otherwise;
--   3. (c) $\pi_M(2) \ge \pi_M^I(1)$ if $c_e \le \frac{1}{1+\phi}$, and $\pi_M(2) < \pi_M^I(1)$ otherwise.
--
--   These comparisons determine the equilibria of the contracting games in Propositions 6–8.
--
--   **Formalization Note** The production economy model takes $c = -c_e$ with $0 < c_e < 2/(1+\phi)$ (the Assumption of p. 251). The ex ante profits are those of an equilibrium of the pricing game on the signal model, not the closed forms: the closed forms are the content of the §4.2 milestones. The production cost is the uncapped quadratic $bq - c_e q^2$ (the paper's cap at $\bar q = b/(2c_e)$ is assumed never to bind, footnote 11, p. 251). **Correction of the paper.** The single value $c_e^* = \frac{2+3\phi}{(1+2\phi)(1+\phi)}$ (which lies in $(1/(1+\phi), 2/(1+\phi))$) is excluded: there the slope $\phi(1+(1+\phi)c)/[(1+\phi)(2+(1+\phi)c)]$ of the best response (2) equals $-1$, so the pricing stage has a continuum of equilibria with different ex ante profits, and Lemma 1's uniqueness claim, on which the payoff table rests, fails.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 259, Lemma 5(a)–(c)

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_PayoffTable
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Economy

/-- **Lemma 5(a)–(c)** (Shang, Ha & Tong 2016, p. 259), production economy (`c = −c_e`) under
the Assumption `c_e < 2/(1+φ)`, stated on the payoff table of every family of pricing
equilibria. For manufacturer `i`: `π_M(0)` is his profit when nobody is informed, `π_M(2)` when
both are, `π_M^I(1)` when he alone is, `π_M^U(1)` when only his rival is. The threshold `c_e^a`
depends only on `φ`.

**Correction.** The value `c_e = (2+3φ)/((1+2φ)(1+φ))` is excluded: there the best-response
slope in (2) is `−1`, the pricing stage has a continuum of equilibria with different ex ante
profits, and Lemma 1's uniqueness (on which the paper's payoff table rests) fails. -/
theorem lemma_5_abc :
    ∀ φ : ℝ, 0 < φ → ∃ ca : ℝ, 1 / (1 + φ) < ca ∧ ca < 2 / (1 + φ) ∧
    ∀ (ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ)
      (E : (Fin 2 → Status) → PricingProfile),
      c = -ce → 0 < ce → ce < 2 / (1 + φ) → ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)) →
      IsSignalModel μ θ Y σ β →
      IsPricingEqFamily μ θ Y a b c φ β E →
      ∀ i : Fin 2,
        let P := payoffTable μ θ Y a b c φ E
        -- (a) π_M^I(1) ≥ π_M(0); π_M(2) ≥ π_M^U(1) iff c_e ≤ c_e^a
        (P.M (fun _ => Status.uninformed) i ≤ P.M (onlyInformed i) i) ∧
        (ce ≤ ca → P.M (onlyInformed (other i)) i ≤ P.M (fun _ => Status.informed) i) ∧
        (ca < ce → P.M (fun _ => Status.informed) i < P.M (onlyInformed (other i)) i) ∧
        -- (b) π_M(0) ≥ π_M^U(1) iff 1/(1+φ) ≤ c_e ≤ (4+5φ)/[(2+3φ)(1+φ)]
        (1 / (1 + φ) ≤ ce → ce ≤ (4 + 5 * φ) / ((2 + 3 * φ) * (1 + φ)) →
          P.M (onlyInformed (other i)) i ≤ P.M (fun _ => Status.uninformed) i) ∧
        (¬ (1 / (1 + φ) ≤ ce ∧ ce ≤ (4 + 5 * φ) / ((2 + 3 * φ) * (1 + φ))) →
          P.M (fun _ => Status.uninformed) i < P.M (onlyInformed (other i)) i) ∧
        -- (c) π_M(2) ≥ π_M^I(1) iff c_e ≤ 1/(1+φ)
        (ce ≤ 1 / (1 + φ) → P.M (onlyInformed i) i ≤ P.M (fun _ => Status.informed) i) ∧
        (1 / (1 + φ) < ce → P.M (fun _ => Status.informed) i < P.M (onlyInformed i) i) := by sorry

end InfoSharing.Economy
