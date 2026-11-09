-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_self_reduction
-- name    : MultiSpinCounting.Positive.self_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:17.180413+00:00
-- url     : https://prove2.me/theorems/c153a4ab-f8b2-46db-bc85-5365a14f192a
-- title:
--   §4.2 — partition function self-reduction identity
-- statement:
--   Let $\Phi$ have positive real data and a fixed complete configuration $\sigma$. In the fixed vertex order, let $\Phi^{(j)}$ retain vertices $v_j,\ldots,v_n$ with fields
--   $$\lambda^{(j)}_u(a)=\lambda_u(a)\prod_{k<j,\{v_k,u\}\in E}A_{v_k,u}(\sigma(v_k),a),\qquad p_j=\mu_{\Phi^{(j)}}(v_j\leftarrow\sigma(v_j)).$$
--   Then
--   $$Z(\Phi)=w(\sigma)\prod_{j=1}^np_j^{-1},\qquad S_r(G^{(j)})\le S_r(G)\quad\text{for every }r\ge0.$$
--   Consequently the original walk bound remains applicable with its original size parameter. The formula uses the explicitly constructed pinned fields, not independent conditional-probability variables.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and spin sets → Fin n and Fin q, with an active vertex subset; reason: relabeling preserves every instance; active subsets implement the source sub-instances and the fixed vertex order
--   - generalization: the paper’s nonempty multi-spin inputs → all finite graphs including the empty graph, and q ≥ 1; reason: the empty products equal one; the identity specializes to all source inputs
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 17, §4.2, unnumbered self-reduction display

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Instance

namespace MultiSpinCounting.Positive

/-- §4.2, p. 17, the unnumbered self-reduction display and its subgraph walk bound. -/
theorem self_reduction {n q : ℕ} (hq : 0 < q) (Φ : Instance n q ℝ)
    (hfull : Φ.active = Finset.univ) (hΦ : IsPositive Φ) (σ : Fin n → Fin q) :
    partition Φ = weight Φ (fun u => σ u.val) *
      ∏ j : Fin n, (marginal (outerPinned Φ σ j.val) j (σ j))⁻¹ ∧
    (∀ (j r : ℕ), sawMax (outerPinned Φ σ j) r ≤ sawMax Φ r) := by sorry

end MultiSpinCounting.Positive
