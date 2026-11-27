-- Prove2me | Theorems.Thm_IncentiveFinNet_Supplement_theorem_9
-- name    : IncentiveFinNet.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:35:58.724663+00:00
-- url     : https://prove2.me/theorems/3c043cd8-432b-5269-a23d-19ee8ceff851
-- title:
--   Theorem 9 — the price increments of pairwise negotiations follow $\mathrm{vec}(\Delta(t+1)) = R(I-\eta L^{\dagger}K)\,\mathrm{vec}(\Delta(t))$
-- statement:
--   Consider a network setting, a dampening factor $\eta\in\mathbb R$ and a skew-symmetric initial price matrix $P(0)$, and let $P(t)$ be the iterates of pairwise negotiations (Algorithm 1 with the price of Proposition 4). Let $K$, $L$, $L^{\dagger}$ and $R$ be the $n^2\times n^2$ matrices
--
--   $$
--   K = \sum_{r=1}^n\bigl(e_re_r^{\top}\otimes Q_r + Q_r\otimes e_re_r^{\top}\bigr),\qquad L_{(i,j),(i,j)} = Q_{i;j,j}+Q_{j;i,i},\qquad R_{(i,j),(i,j)} = s_{ij},
--   $$
--
--   with $L$ and $R$ diagonal, $s_{ij}=1$ if $\{i,j\}$ is a permitted edge and $0$ otherwise, and $L^{\dagger}$ the pseudoinverse of $L$. Write $\Delta(t) = P(t)-P(t-1)$. Then for every $t\ge1$
--
--   $$
--   \mathrm{vec}\bigl(\Delta(t+1)\bigr) = R\bigl(I_{n^2}-\eta L^{\dagger}K\bigr)\mathrm{vec}\bigl(\Delta(t)\bigr).
--   $$
--
--   The price increments thus evolve by a fixed linear map, whose spectrum governs the convergence of pairwise negotiations (Theorem 4).
--
--   Differences from the source:
--
--   - encoding: Δ(t+1) = P(t+1) − P(t) at every time step → the identity for every t ≥ 1, with Δ(t) = P(t) − P(t − 1); reason: Δ(t) is defined only for t ≥ 1; same instances
--   - encoding: pairwise negotiations from Algorithm 1 (P(0) skew-symmetric, η ∈ (0, 1)) → every skew-symmetric P(0) and every real η; reason: the theorem fixes no range for η and the identity holds for every η; Algorithm 1 starts from a skew-symmetric P(0)
--   - encoding: s_ij for a permitted edge {i, j}; positions (i − 1)n + j; vec → s_ij = 1 iff j ∈ J_i (so (i, i) counts when i ∈ J_i); positions as pairs (i, j); vecPair (column stacking); reason: Lean convention; a self-investment is the edge {i, i}
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 9, A.8, pp.38–39

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Q
import Definitions.Def_IncentiveFinNet_Supplement_negotiate
import Definitions.Def_IncentiveFinNet_Supplement_matK

open Matrix

namespace IncentiveFinNet.Supplement

/-- **Theorem 9**, Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3, A.8, pp.38–39: "Let `s_ij = 1`
if `{i, j}` is a permitted edge and `0` otherwise. Let `L, R ∈ ℝ^{n²×n²}` be diagonal matrices such
that `L_{(i−1)n+j,(i−1)n+j} = Q_{i;jj} + Q_{j;ii}` and `R_{(i−1)n+j,(i−1)n+j} = s_ij`, and `L†` be the
pseudoinverse of `L`. Let `Δ(t+1) = P(t + 1) − P(t)`, where `P(t)` is the price matrix at time step
`t` of pairwise negotiations. Then, `vec(Δ(t+1)) = R(I_{n²} − ηL†K) vec(Δ(t))`, where
`K = Σ_{r=1}^n (e_r e_rᵀ ⊗ Q_r + Q_r ⊗ e_r e_rᵀ)`."

Stated for every network setting, every real `η`, every skew-symmetric `P(0)` and every `t ≥ 1`;
`P(t)` is `negotiate S η P₀ t` (Algorithm 1 with the price of Proposition 4).

**Formalization Note** `vec` is `vecPair` (column stacking, pairs `(i, j)` for positions
`(i − 1)n + j`); `K`, `L†`, `R` are `matK`, `matLpinv`, `matR`. `Δ(t) = P(t) − P(t − 1)` is defined
only for `t ≥ 1`, hence `1 ≤ t`. -/
theorem theorem_9 {n : ℕ} (S : NetworkSetting n) (η : ℝ) (P₀ : Matrix (Fin n) (Fin n) ℝ)
    (hP₀ : P₀ᵀ = -P₀) (t : ℕ) (ht : 1 ≤ t) :
    vecPair (negotiate S η P₀ (t + 1) - negotiate S η P₀ t) =
      (matR S * (1 - η • (matLpinv S * matK S))) *ᵥ
        vecPair (negotiate S η P₀ t - negotiate S η P₀ (t - 1)) := by sorry

end IncentiveFinNet.Supplement
