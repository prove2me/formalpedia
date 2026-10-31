-- Prove2me | Theorems.Thm_LongShortSI_lemma_EC_1
-- name    : LongShortSI.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:41.409896+00:00
-- url     : https://prove2.me/theorems/ebfef1ae-1461-4bdd-b2f0-686b8fff916c
-- title:
--   Lemma EC.1 — the reseller's period-2 purchases (EC.2) are the unique optimum (corrected: (EC.1) index)
-- statement:
--   Let $a>0$ and $0\le d<1$. In stage 2b of the SS game the reseller holds inventories $I_A,I_B\ge0$, faces second-period prices $w_{A2},w_{B2}\ge0$, and chooses purchases $q_{A2},q_{B2}\ge0$ to maximize her period-2 profit
--   $$
--   \pi_2(q)=\sum_{i\in\{A,B\},\,j\ne i}\bigl(a-(q_{i2}+I_i)-d(q_{j2}+I_j)\bigr)(q_{i2}+I_i)-w_{i2}q_{i2}.
--   $$
--   With $\bar w_{i2}(I_i,w_{j2})=a(1-d)-2(1-d^2)I_i+dw_{j2}$ and $\widehat w_{i2}(I_i,I_j)=a-2(I_i+dI_j)$, the purchases
--   $$
--   q^{SS}_{i2}=\begin{cases}\dfrac{a(1-d)-2(1-d^2)I_i-w_{i2}+dw_{j2}}{2(1-d^2)} & w_{i2}\le\bar w_{i2}(I_i,w_{j2}),\ w_{j2}\le\bar w_{j2}(I_j,w_{i2}),\\[2mm] \dfrac{a-w_{i2}-2(I_i+dI_j)}{2} & w_{i2}\le\widehat w_{i2}(I_i,I_j),\ w_{j2}>\bar w_{j2}(I_j,w_{i2}),\\[1mm] 0 & \text{otherwise}\end{cases}\tag{EC.2}
--   $$
--   are non-negative and are the unique maximizer of $\pi_2$ over all non-negative purchases.
--
--   This is the last stage of the backward induction for short-term contracts; the suppliers' period-2 pricing game (Lemma EC.2) is played against this response.
--
--   Differences from the source:
--   - correction: objective (EC.1): Σ (a − (q_i2 + I_i) − d(q_j2 + I_j))(q_j2 + I_j) − w_i2 q_i2 → the period-2 part of (3): Σ (a − (q_i2 + I_i) − d(q_j2 + I_j))(q_i2 + I_i) − w_i2 q_i2; reason: with the printed index, at a = 1, d = 0, I = 0, w = 0 the objective is q_A + q_B − 2q_A q_B, unbounded above (q = (t, 0), t → ∞ gives t), so (EC.2) would not be optimal; (3) on p.9 has (q_i2 + I_i)
--   - reading: "the reseller's optimal purchase quantities … is given by (EC.2)" → for I ≥ 0 and w ≥ 0, (EC.2) is non-negative and the unique maximizer of the period-2 profit over q ≥ 0; reason: the objective is strictly concave for d < 1, so "the optimal quantities" is the unique maximizer; prices and inventories are non-negative in the game
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), E-Companion, Lemma EC.1 and (EC.1)–(EC.2), p.ec1 (PDF 33)

import Mathlib
import Definitions.Def_LongShortSI_Model
import Definitions.Def_LongShortSI_ClosedForms

open scoped NNReal

namespace LongShortSI

/-- **Lemma EC.1, p.ec1 (PDF 33) — the reseller's period-2 purchases.**
Roy–Gilbert–Lai, SSRN 3752131 (version of 2022-04-20).

For `a > 0`, `d ∈ [0, 1)`, inventories `I ≥ 0` and second-period prices `w ≥ 0`, the purchases
(EC.2) are non-negative and are the unique maximizer of the reseller's period-2 profit
`Σ_i (p_i2 s_i2 − w_i2 q_i2)`, `s_i2 = q_i2 + I_i`, over all non-negative purchases.

**Formalization Note** The objective is the period-2 part of (3); the printed (EC.1) has the index
`j` in place of `i` in the quantity factor (correction C6). -/
theorem lemma_EC_1 (a d : ℝ) (ha : 0 < a) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (I w : Product → ℝ) (hI : Nonneg I) (hw : Nonneg w) :
    Nonneg (q2EC2 a d I w) ∧
    (∀ q, Nonneg q → resellerProfit2 a d I w q ≤ resellerProfit2 a d I w (q2EC2 a d I w)) ∧
    (∀ q, Nonneg q → resellerProfit2 a d I w q = resellerProfit2 a d I w (q2EC2 a d I w) →
      q = q2EC2 a d I w) := by sorry

end LongShortSI
