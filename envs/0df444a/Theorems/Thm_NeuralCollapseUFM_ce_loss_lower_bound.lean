-- Prove2me | Theorems.Thm_NeuralCollapseUFM_ce_loss_lower_bound
-- name    : NeuralCollapseUFM.ce_loss_lower_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:16:45.00486+00:00
-- url     : https://prove2.me/theorems/022b5561-3a69-4c9b-b3ff-4d8d155e084b
-- title:
--   Lemma B.5 (as proved): lower bound for the cross-entropy loss and its equality case
-- statement:
--   Let $K\ge2$, $z\in\mathbb{R}^K$, $k\in[K]$ and $c_1>0$, and let $c_2=\frac1{1+c_1}\log\big((1+c_1)(K-1)\big)+\frac{c_1}{1+c_1}\log\frac{1+c_1}{c_1}$. Then
--
--   $$\mathcal L_{CE}(z,y_k)\ge\frac1{1+c_1}\,\frac{\big(\sum_{i=1}^Kz_i\big)-Kz_k}{K-1}+c_2,$$
--
--   with equality if and only if $z_i=z_j$ for all $i,j\ne k$ and
--
--   $$c_1=\Big[(K-1)\exp\Big(\frac{(\sum_{i=1}^Kz_i)-Kz_k}{K-1}\Big)\Big]^{-1}.$$
--
--   This is a lower bound for the cross-entropy that is linear in the logits; it drives the proof of Theorem 3.1.
--
--   **Formalization Note** The paper states that equality holds "when" these conditions hold. Its proof shows both directions, and Lemma B.4 uses the "only if" direction, so the equivalence is stated.
-- source:
--   Zhu, Ding, Zhou, Li, You, Sulam and Qu, A Geometric Analysis of Neural Collapse with Unconstrained Features, arXiv:2105.02375v1 (2021), Appendix B.2, Lemma B.5, eqs. (34)-(35), p. 36

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Matrix Filter Topology

namespace NeuralCollapseUFM

theorem ce_loss_lower_bound {K : ℕ} (hK : 2 ≤ K) (z : Fin K → ℝ) (k : Fin K) (c1 : ℝ)
    (hc1 : 0 < c1) :
    1 / (1 + c1) * ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) + cTwo K c1 ≤ ceLoss z k ∧
    (ceLoss z k = 1 / (1 + c1) * ((∑ i, z i) - K * z k) / ((K : ℝ) - 1) + cTwo K c1 ↔
      (∀ i j, i ≠ k → j ≠ k → z i = z j) ∧
        c1 = (((K : ℝ) - 1) * Real.exp (((∑ i, z i) - K * z k) / ((K : ℝ) - 1)))⁻¹) := by sorry

end NeuralCollapseUFM
