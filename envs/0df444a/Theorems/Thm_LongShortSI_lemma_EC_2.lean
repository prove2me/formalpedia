-- Prove2me | Theorems.Thm_LongShortSI_lemma_EC_2
-- name    : LongShortSI.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:51.359909+00:00
-- url     : https://prove2.me/theorems/aa38920d-20cf-4d6e-84b3-40122b42e540
-- title:
--   Lemma EC.2 — the period-2 wholesale prices (EC.4) form the stage-2a equilibrium
-- statement:
--   Let $a>0$, $0\le d<1$, and let the reseller respond optimally in stage 2b. Write
--   $$
--   \bar I_j(I_i)=\tfrac14\Bigl(\tfrac{a(2+d)}{1+d}-2dI_i\Bigr),\qquad \widehat I_j(I_i)=\frac{a(2-d)-2dI_i}{2(2-d^2)},\qquad \widetilde I_j(I_i)=\frac{a-2I_i}{2d},
--   $$
--   and let $w^{SS}_{i2}(I_i,I_j)$ be
--   $$
--   \begin{cases}\dfrac{(1-d)(a(2+d)-2(1+d)(2I_i+dI_j))}{4-d^2} & I_i<\bar I_i(I_j),\ I_j<\bar I_j(I_i),\\[2mm] \dfrac{(1-d)(2(1+d)I_j-a)}{d} & I_i<\bar I_i(I_j),\ I_j\in[\bar I_j(I_i),\widehat I_j(I_i)),\\[2mm] \dfrac{a-2(I_i+dI_j)}{2} & I_i<\bar I_i(I_j),\ I_j\in[\widehat I_j(I_i),\widetilde I_j(I_i)),\\[1mm] 0 & \text{otherwise.}\end{cases}\tag{EC.4}
--   $$
--
--   1. At $I_i=\frac{a}{2(1+d)}$: $\bar I_j(I_i)=\widehat I_j(I_i)=\widetilde I_j(I_i)=\frac{a}{2(1+d)}$.
--   2. If $I_i\ge\frac{a}{2(1+d)}$ for both products, the reseller buys nothing at any non-negative prices.
--   3. If $I_i<\frac{a}{2(1+d)}$ for at least one product, the prices (EC.4) are non-negative and form a pure Nash equilibrium of the suppliers' period-2 pricing game (each supplier earns $w_{i2}q_{i2}$), and every Nash equilibrium of that game gives the same purchases and the same supplier profits as (EC.4).
--
--   Together with Lemma EC.1 this gives the period-2 continuation that the reseller anticipates when she decides how much to stock.
--
--   **Formalization Note** The upper end $\widetilde I_j$ is used as the condition $2dI_j<a-2I_i$, and its identity in 1 as $2d\cdot\frac{a}{2(1+d)}=a-\frac{2a}{2(1+d)}$; for $d>0$ these are the printed conditions.
--
--   Differences from the source:
--   - reading: "the suppliers' wholesale prices satisfy (EC.4)" → (EC.4) is a Nash equilibrium of stage 2a, and every Nash equilibrium gives the same purchases and the same supplier profits; reason: on the third branch the supplier who sells nothing is indifferent among prices, so the prices themselves are not unique; purchases and profits are what the backward induction uses
--   - reading: "neither supplier can induce the reseller to purchase additional units at a non-negative wholesale price" → for every non-negative price pair, every optimal stage-2b response buys 0 of both products; reason: literal content of the sentence, stated against any optimal stage-2b strategy
--   - encoding: Ĩ_j(I_i) = (a − 2I_i)/(2d) and the identity Ĩ_j = a/(2(1 + d)) at I_i = a/(2(1 + d)) → the condition 2dI_j < a − 2I_i and the identity 2d·a/(2(1 + d)) = a − 2a/(2(1 + d)); reason: equivalent for d > 0; at d = 0 the printed fraction divides by zero, and the multiplicative form keeps d = 0 in the domain
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), E-Companion, Lemma EC.2 and (EC.4), p.ec2 (PDF 34)

import Mathlib
import Definitions.Def_LongShortSI_Model
import Definitions.Def_LongShortSI_ClosedForms

open scoped NNReal

namespace LongShortSI

/-- **Lemma EC.2, p.ec2 (PDF 34) — the period-2 wholesale prices.**
Roy–Gilbert–Lai, SSRN 3752131 (version of 2022-04-20).

Let `a > 0`, `d ∈ [0, 1)`, and let `resp2` be any optimal stage-2b strategy of the reseller.
1. `Ī_j(I_i) = Î_j(I_i) = Ĩ_j(I_i) = a/(2(1 + d))` at `I_i = a/(2(1 + d))`;
2. if `I_i ≥ a/(2(1 + d))` for both products, the reseller buys nothing at any non-negative prices;
3. if `I_i < a/(2(1 + d))` for some product, the prices (EC.4) are non-negative and form a Nash
   equilibrium of the stage-2a pricing game, and every Nash equilibrium of that game yields the
   same purchases and the same supplier profits as (EC.4).

**Formalization Note** "The suppliers' wholesale prices satisfy (EC.4)" is read as 3: a supplier
who sells nothing on the third branch is indifferent among prices, so the prices themselves are not
unique. `Ĩ_j(I_i) = (a − 2I_i)/(2d)` is encoded multiplicatively (see `wEC4`), and its identity
in 1 is stated as `2d·a/(2(1 + d)) = a − 2a/(2(1 + d))`. -/
theorem lemma_EC_2 (a d : ℝ) (ha : 0 < a) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (resp2 : (Product → ℝ) → (Product → ℝ) → (Product → ℝ)) (h2b : Stage2bOptimal a d resp2) :
    (Ibar a d (a / (2 * (1 + d))) = a / (2 * (1 + d)) ∧
      Ihat a d (a / (2 * (1 + d))) = a / (2 * (1 + d)) ∧
      2 * d * (a / (2 * (1 + d))) = a - 2 * (a / (2 * (1 + d)))) ∧
    (∀ I, Nonneg I → (∀ i, a / (2 * (1 + d)) ≤ I i) →
      ∀ w2, Nonneg w2 → ∀ i, resp2 I w2 i = 0) ∧
    (∀ I, Nonneg I → (∃ i, I i < a / (2 * (1 + d))) →
      0 ≤ wEC4 a d I .A ∧ 0 ≤ wEC4 a d I .B ∧
      CompetingChains.Cournot.IsPureNash (stage2Payoff resp2 I .A) (stage2Payoff resp2 I .B)
        (wEC4 a d I .A).toNNReal (wEC4 a d I .B).toNNReal ∧
      ∀ xA xB : ℝ≥0,
        CompetingChains.Cournot.IsPureNash (stage2Payoff resp2 I .A) (stage2Payoff resp2 I .B)
          xA xB →
        resp2 I (pair (xA : ℝ) (xB : ℝ)) = resp2 I (pair (wEC4 a d I .A) (wEC4 a d I .B)) ∧
        ∀ i, stage2Payoff resp2 I i xA xB =
          stage2Payoff resp2 I i (wEC4 a d I .A).toNNReal (wEC4 a d I .B).toNNReal) := by sorry

end LongShortSI
