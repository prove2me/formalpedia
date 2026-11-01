-- Prove2me | Theorems.Thm_MNLStability_scale_no_purchase
-- name    : MNLStability.scale_no_purchase
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:55.802062+00:00
-- url     : https://prove2.me/theorems/605cf3d9-f581-42db-b4cd-ae18698d0706
-- title:
--   Proof of Lemma 5 — scaling down $w_0$ raises every product's expected demand
-- statement:
--   Scale the no-purchase weight to $\tilde w_0=(1-\varepsilon)w_0$, $\varepsilon\in[0,1)$, keeping every product weight. For any inventory vector $U$ and every product $i$,
--
--   $$\mathbb E_{\tilde w}[X_i^U]\ \ge\ \mathbb E_w[X_i^U].$$
--
--   Step 2 of the proof of Lemma 5 rounds down "the weight $w^\uparrow_i$ of each product $i$, including the no-purchase option" and says the loss "has already been accounted for in Section 3.1". Section 3.1 and Theorem 2 only scale products, so the step for the no-purchase option is this statement: the no-purchase option behaves as a product with infinite inventory and zero price.
--
--   Differences from the source:
--   - generalization: the standing assumption of §2.3, p.13 ("in the remainder of this paper, we operate under the opposite scenario of w_max > εw₀/n") → no regime hypothesis; reason: the proof uses no lower bound on purchase probabilities; every instance of the regime is covered
--   - reading: "the weight w↑_i of each product i, including the no-purchase option, is rounded down … already been accounted for in Section 3.1" → scaling w₀ by 1 − ε can only raise every product's expected demand; reason: the step uses this fact for the no-purchase option, which Theorem 2 (a product scaling) does not cover
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), proof of Lemma 5, step 2, p.17

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_scaleProd

namespace MNLStability

/-- **Scaling the no-purchase weight** (SSRN:3498325, proof of Lemma 5, step 2, p.17: "the weight
`w↑_i` of each product `i`, including the no-purchase option, is rounded down"). Scale the
no-purchase weight to `(1 − ε)·w₀`, `ε ∈ [0, 1)`, keeping every product weight. For any inventory
vector `U` and every product `i`, `E_w̃[X_i^U] ≥ E_w[X_i^U]`. -/
theorem scale_no_purchase {n : ℕ} (wts : Weights n) (hw : wts.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (U : Fin n → ℕ) (i : Fin n) :
    expX wts pM U i ≤ expX (scaleNoPurchase wts ε) pM U i := by sorry

end MNLStability
