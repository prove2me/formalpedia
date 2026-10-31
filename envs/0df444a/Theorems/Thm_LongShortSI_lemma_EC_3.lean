-- Prove2me | Theorems.Thm_LongShortSI_lemma_EC_3
-- name    : LongShortSI.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:44.942888+00:00
-- url     : https://prove2.me/theorems/4a68b21b-7288-4b60-8143-d599d80e41af
-- title:
--   Lemma EC.3 — the reseller's period-1 response: sales (EC.6) and the inventory thresholds (corrected: $\bar w^{SS}_{i1}$ divided by $12-d^2$; strict inequalities)
-- statement:
--   Let $a>0$, $0\le d<1$, $h\ge0$, and let the period-2 continuation be an equilibrium one (optimal stage-2b purchases and Nash stage-2a prices at every inventory). Define
--   $$
--   \bar w^{SS}_{i1}(w_{j1})=\frac{(3+d)\bigl(a(3-d)(1-d)-(2-d)^2h\bigr)+d(8-d^2)w_{j1}}{12-d^2},\qquad \bar{\bar w}_{i1}(w_{j1})=a(1-d)+dw_{j1}.
--   $$
--   Then $\bar w^{SS}_{i1}(w_{j1})\le\bar{\bar w}_{i1}(w_{j1})$ for $w_{j1}\ge0$, and for all first-period prices $w_{A1},w_{B1}\ge0$ with $w_{A1}\le\bar{\bar w}_{A1}(w_{B1})$ and $w_{B1}\le\bar{\bar w}_{B1}(w_{A1})$:
--
--   1. the reseller has a best response, and every best response sells
--   $$
--   s^{SS}_{i1}(w_{i1},w_{j1})=\frac{a(1-d)-w_{i1}+dw_{j1}}{2(1-d^2)};\tag{EC.6}
--   $$
--   2. if $w_{A1}<\bar w^{SS}_{A1}(w_{B1})$ and $w_{B1}<\bar w^{SS}_{B1}(w_{A1})$, every best response holds positive inventory of both products;
--   3. if $w_{i1}>\bar w^{SS}_{i1}(w_{j1})$, every best response holds no inventory of product $i$, and holds inventory of product $j$ if and only if $w_{j1}<\frac{a(3-d)(1-d)}{(2-d)^2}-h$.
--
--   The lemma describes how first-period prices steer the reseller's strategic inventory, which is what each supplier weighs in stage 1a.
--
--   Differences from the source:
--   - reading: model conventions left implicit (pp.6–9) → "equilibrium" is a pure-strategy subgame-perfect equilibrium; wholesale prices range over [0, ∞); all quantities are ≥ 0; all stock is sold in period 2 (s_i2 = q_i2 + I_i) with no free disposal and no floor on market prices; production and selling costs are 0; the holding cost h is ≥ 0; reason: p.6 ("no units are salvaged", costs normalized to zero), ec2 ("at a non-negative wholesale price"), p.12 ("any non-negative holding cost") and ec6 ("for any 0 ≤ h < h^{SS}_I(d)"); the paper solves the game by backward induction
--   - reading: SS game: suppliers observe the reseller's inventory before period 2 (§3.1, p.8) → period-2 strategies are functions of the inventories (I_A, I_B) (and, for the reseller, of the period-2 prices); reason: the period-2 payoffs depend on nothing else; the paper's backward induction (ec1–ec4) uses exactly these histories
--   - correction: w̄^{SS}_i1(w_j1) := ((3 + d)(a(3 − d)(1 − d) − (2 − d)²h) + d(8 − d²)w_j1)(12 − d²) → the same numerator divided by (12 − d²); reason: the threshold is the root of I^{SS}_{iFOC} = 0 on the same page; at a = 1, d = 0, h = 0, w_j1 = 0 the printed form gives 108 > w̿ = 1, contradicting the lemma's own w̄^{SS} ≤ w̿, while the quotient is 3/4
--   - correction: (ii) "If w_A1 ≤ w̄^{SS}_A1(w_B1) and w_B1 ≤ w̄^{SS}_B1(w_A1), then the reseller holds a positive inventory of both products" → strict inequalities w_A1 < w̄^{SS}_A1(w_B1), w_B1 < w̄^{SS}_B1(w_A1); reason: at equality the inventory is zero: a = 1, d = 0, h = 0, w_A1 = 3/4 = w̄^{SS}_A1 gives I_A = 1/2 − (2/3)(3/4) = 0
--   - reading: "If either of these inequalities is reversed, then the reseller holds no inventory of the product with the higher wholesale price, and holds inventory of the other one only if its wholesale price is sufficiently small" → if w_i1 > w̄^{SS}_i1(w_j1), every best response has I_i = 0, and I_j > 0 iff w_j1 < a(3 − d)(1 − d)/(2 − d)² − h; reason: the threshold is where I^{SS}_{jNIi} of the proof (ec4) vanishes; the product whose inequality is reversed is the one with the higher price whenever the other holds inventory
--   - reading: "the reseller's best response … is to sell (EC.6) and to hold inventory that depends as follows" → a best response exists, and every best response (against any equilibrium continuation) sells (EC.6) and satisfies 2–3, for prices in the region of (i); reason: the paper restricts attention to price pairs with w ≤ w̿ (ec3, before the lemma); part (ii) is stated within that restriction
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), E-Companion, Lemma EC.3 and (EC.6), p.ec3 (PDF 35); I^{SS}_{iNIj} in its proof, p.ec4 (PDF 36)

import Mathlib
import Definitions.Def_LongShortSI_Model
import Definitions.Def_LongShortSI_ClosedForms

open scoped NNReal

namespace LongShortSI

/-- **Lemma EC.3, p.ec3 (PDF 35) — the reseller's period-1 response** (corrected: C4, C5).
Roy–Gilbert–Lai, SSRN 3752131 (version of 2022-04-20).

Let `a > 0`, `d ∈ [0, 1)`, `h ≥ 0`, and let `(resp2, price2)` be any equilibrium continuation
(optimal stage-2b purchases, Nash stage-2a prices at every inventory). Then
`w̄^{SS}_i1(w_j1) ≤ w̿_i1(w_j1)` for `w_j1 ≥ 0`, and for every non-negative pair `(w_A1, w_B1)`
with `w_A1 ≤ w̿_A1(w_B1)` and `w_B1 ≤ w̿_B1(w_A1)`:
1. the reseller has a best response, and every best response sells (EC.6);
2. if `w_A1 < w̄^{SS}_A1(w_B1)` and `w_B1 < w̄^{SS}_B1(w_A1)`, every best response holds positive
   inventory of both products;
3. if `w_i1 > w̄^{SS}_i1(w_j1)`, every best response holds no inventory of `i`, and holds inventory of
   `j` if and only if `w_j1 < a(3 − d)(1 − d)/(2 − d)² − h`.

**Formalization Note** `w̄^{SS}_i1` is divided by `12 − d²` (C4) and "positive inventory" needs
strict inequalities (C5). "Only if its wholesale price is sufficiently small" is pinned from the
proof (ec4, `I^{SS}_{iNIj} > 0`). Part 3 states "the product with the higher wholesale price" as
the product whose inequality is reversed. -/
theorem lemma_EC_3 (a d h : ℝ) (ha : 0 < a) (hd0 : 0 ≤ d) (hd1 : d < 1) (hh : 0 ≤ h)
    (resp2 : (Product → ℝ) → (Product → ℝ) → (Product → ℝ))
    (price2 : (Product → ℝ) → ℝ≥0 × ℝ≥0)
    (h2b : Stage2bOptimal a d resp2) (h2a : Stage2aNash resp2 price2) :
    (∀ wj, 0 ≤ wj → wbarSS1 a d h wj ≤ wbbar1 a d wj) ∧
    ∀ w1 : Product → ℝ, Nonneg w1 → (∀ i, w1 i ≤ wbbar1 a d (w1 i.other)) →
      (∃ y, Period1BestResponse a d h resp2 price2 w1 y) ∧
      ∀ y, Period1BestResponse a d h resp2 price2 w1 y →
        (∀ i, y.s1 i = s1EC6 a d (w1 i) (w1 i.other)) ∧
        ((∀ i, w1 i < wbarSS1 a d h (w1 i.other)) → ∀ i, 0 < y.inv i) ∧
        (∀ i, wbarSS1 a d h (w1 i.other) < w1 i →
          y.inv i = 0 ∧
          (0 < y.inv i.other ↔ w1 i.other < a * (3 - d) * (1 - d) / (2 - d) ^ 2 - h)) := by sorry

end LongShortSI
