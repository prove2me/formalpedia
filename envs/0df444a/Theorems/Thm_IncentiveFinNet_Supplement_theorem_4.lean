-- Prove2me | Theorems.Thm_IncentiveFinNet_Supplement_theorem_4
-- name    : IncentiveFinNet.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:33:06.071523+00:00
-- url     : https://prove2.me/theorems/a5822c6a-b293-58cf-b38b-34a3706692df
-- title:
--   Theorem 4 — convergence of pairwise negotiations for $\eta\in(0,2/\lambda_{\max})$ (corrected: rate in the $L$-weighted norm; the limit is a stable price when $P(0)$ vanishes on prohibited pairs)
-- statement:
--   Consider a network setting in which at least one pair $(i,j)$ with $j\in J_i$ is permitted. Let $K$, $L$, $L^{\dagger}$, $(L^{\dagger}K)|_R$, $\lambda_{\max}$, $\lambda_{\min}$ be as in the theorem, $\eta^* = 2/\lambda_{\max}$, and for $\eta\in(0,\eta^*)$ let
--
--   $$
--   \alpha = \max\{|1-\eta\lambda_{\min}|,\ |1-\eta\lambda_{\max}|\}.
--   $$
--
--   Let $P(t)$ be the iterates of pairwise negotiations (Algorithm 1 with the price of Proposition 4). Then for every $\eta\in(0,\eta^*)$:
--
--   1. pairwise negotiations with $\eta$ are **globally asymptotically stable** (Definition 6): for every skew-symmetric $P(0)$ there is $P^\star$ with $\|P(t)-P^\star\|_F\to0$;
--   2. for every skew-symmetric $P(0)$, every such limit $P^\star$ and every $t\ge0$,
--   $$
--   \|P(t)-P^\star\|_L \le \frac{\alpha^t}{1-\alpha}\,\|P(1)-P(0)\|_L ,
--   $$
--   where $\|X\|_L^2=\sum_{(i,j):\,j\in J_i}(Q_{i;j,j}+Q_{j;i,i})X_{ij}^2$;
--   3. if moreover $P(0)$ vanishes on the prohibited pairs, then $P^\star$ is the price matrix of a stable point: $(W,P^\star)$ is stable for the best-response network $W_{ij} = e_i^{\top}Q_j(M-P^\star)e_j$.
--
--   The negotiation process, which needs no knowledge of the other agents' beliefs, converges for every dampening factor below $2/\lambda_{\max}$, at a geometric rate, to the stable point of Theorem 1.
--
--   Differences from the source:
--
--   - correction: part 2: ‖P(t) − P⋆‖_F ≤ αᵗ/(1 − α)·‖P(1) − P(0)‖_F (Frobenius norm) → the same bound, with the same α and factor αᵗ/(1 − α), in the L-weighted norm ‖X‖_L² = Σ_{j∈J_i}(Q_i;j,j + Q_j;i,i)X_ij²; reason: the printed bound is false: for n = 3, J_1 = {1,2}, J_2 = {1,3}, J_3 = {2,3}, the integer Σ_i, γ = (4, 2, 1/2) and M of 02-supplement/theorem4_part2_check.py, η = η*/2 and P(0) = 0, ‖P(0) − P⋆‖_F ≈ 2.937 > 2.812 ≈ α⁰/(1 − α)·‖P(1) − P(0)‖_F, and it fails again at t = 1, 2, 3; the proof (p.41) uses the spectral radius of the non-symmetric R(I − ηL†K) as an operator norm, which is valid in ‖·‖_L, where that matrix is self-adjoint on the permitted positions. No case is excluded
--   - correction: "Here, P⋆ is the stable point to which the negotiation converges" (for any skew-symmetric P(0)) → if P(0) vanishes on the prohibited pairs, (bestResponse P⋆, P⋆) is stable; reason: prohibited entries never change (A.8, p.39), so for P(0) nonzero on a prohibited pair (n = 2, J_1 = {1}, J_2 = {2}, P(0)_12 = 1 = −P(0)_21) P⋆ is nonzero there and no feasible point has price P⋆; excluded case: part 3 for P(0) nonzero on a prohibited pair (parts 1 and 2 keep every skew-symmetric P(0))
--   - reading: "P⋆ is the stable point" → the price matrix P⋆ together with the best-response network W_ij = e_iᵀQ_j(M − P⋆)e_j is a stable point; reason: P⋆ is the limit of price matrices; p.15 says all agents agree on their contract sizes at P⋆, i.e. the network is the agents' optimal contracts
--   - reading: Definition 6: "for any initial price matrix P(0)" → every skew-symmetric P(0); reason: Algorithm 1, line 3, starts from any skew-symmetric matrix, and the text after Definition 6 uses that every P(t) is skew-symmetric
--   - encoding: λ_max, λ_min, the largest and smallest eigenvalues of (L†K)|_R → sSup and sInf of the real spectrum of LKR S, with the hypothesis that some pair (i,j) with j ∈ J_i exists; reason: all eigenvalues are real ((L†K)|_R is similar to a symmetric matrix, p.41); the hypothesis only excludes the case where (L†K)|_R is empty and λ_max is undefined
--   - encoding: P⋆ in part 2, the limit of P(t) → every Frobenius limit P⋆ of P(t); reason: the limit is unique; same instances
--   - encoding: n² × n² matrices indexed by (i − 1)n + j; ‖·‖_F → matrices indexed by pairs (i, j) : Fin n × Fin n; DDROCS.frobNorm; reason: Lean convention; same matrices
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 4, pp.15–16; Remark 1, p.16; Algorithm 1 and Definition 6, p.14; proofs: Propositions 5–6, A.8, pp.41–42

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable
import Definitions.Def_IncentiveFinNet_Q
import Definitions.Def_DDROCS_frobNorm
import Definitions.Def_IncentiveFinNet_Supplement_negotiate
import Definitions.Def_IncentiveFinNet_Supplement_GloballyAsymptoticallyStable
import Definitions.Def_IncentiveFinNet_Supplement_matK
import Definitions.Def_IncentiveFinNet_Supplement_lamMax

open Matrix Filter Topology

namespace IncentiveFinNet.Supplement

/-- **Theorem 4 (Convergence Conditions and Rate)**, Jalan, Chakrabarti, Sarkar,
arXiv:2212.06808v3, pp.15–16 (proved in A.8 as Propositions 5–6, pp.41–42). With `K`, `L`, `L†`,
`(L†K)|_R`, `λ_max`, `λ_min` as printed and `η* = 2/λ_max`:
1. "For all `η ∈ (0, η*)`, pairwise negotiations with `η` are globally asymptotically stable."
2. "For such an `η`, the convergence is exponential in the number of rounds `t`:
   `‖P(t) − P⋆‖_F ≤ αᵗ/(1 − α) · ‖P(1) − P(0)‖_F`, where `α = max{|1 − ηλ_min|, |1 − ηλ_max|}`.
   Here, `P⋆` is the stable point to which the negotiation converges."

Stated for every network setting with at least one permitted pair, every `η ∈ (0, 2/λ_max)` and
every skew-symmetric `P(0)`:
1. `GloballyAsymptoticallyStable S η` (Definition 6);
2. for every limit `P⋆` of `P(t)` in Frobenius norm and every `t ≥ 0`,
   `‖P(t) − P⋆‖_L ≤ αᵗ/(1 − α) · ‖P(1) − P(0)‖_L`;
3. if `P(0)` vanishes on the prohibited pairs, `P⋆` is the price matrix of a stable point:
   `(W, P⋆)` is stable (Definition 3) with `W` the best-response network
   `W_ij = e_iᵀ Q_j (M − P⋆) e_j`.

**Formalization Note**
* Part 2 is stated in the weighted norm `‖X‖_L² = Σ_{j ∈ J_i} (Q_{i;j,j} + Q_{j;i,i}) X_ij²`
  (`normL`), not in the Frobenius norm. The printed Frobenius bound is false: for `n = 3`,
  `J_1 = {1, 2}`, `J_2 = {1, 3}`, `J_3 = {2, 3}`, the integer covariances, `γ = (4, 2, 1/2)` and
  `M` of `missions/02-supplement/theorem4_part2_check.py`, `η = η*/2` and `P(0) = 0`, one has
  `‖P(0) − P⋆‖_F ≈ 2.937 > 2.812 ≈ α⁰/(1 − α)·‖P(1) − P(0)‖_F`. The proof (p.41) bounds
  `‖Δ_{t+1}‖_F ≤ |β| ‖Δ_t‖_F` with the spectral radius `|β|` of the non-symmetric
  `R(I − ηL†K)`; the bound holds in `‖·‖_L`, in which that matrix is self-adjoint on the permitted
  positions, with the paper's `α` and factor `αᵗ/(1 − α)`.
* Part 3 needs `P(0)` to vanish on prohibited pairs: prohibited entries never change (A.8), so
  otherwise `P⋆` is nonzero on a prohibited pair and no feasible point has price `P⋆`.
* `∃ i j, j ∈ J_i` makes `(L†K)|_R` nonempty, so that `λ_max` exists.
* `P(t)` is `negotiate S η P₀ t`; `‖·‖_F` is `DDROCS.frobNorm`. -/
theorem theorem_4 {n : ℕ} (S : NetworkSetting n) (hR : ∃ i j, j ∈ S.J i) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 / lamMax S) :
    GloballyAsymptoticallyStable S η ∧
      ∀ P₀ : Matrix (Fin n) (Fin n) ℝ, P₀ᵀ = -P₀ →
        ∀ Pstar : Matrix (Fin n) (Fin n) ℝ,
          Tendsto (fun t => DDROCS.frobNorm (negotiate S η P₀ t - Pstar)) atTop (𝓝 0) →
          (∀ t : ℕ, normL S (negotiate S η P₀ t - Pstar) ≤
              convRate S η ^ t / (1 - convRate S η) * normL S (negotiate S η P₀ 1 - P₀)) ∧
          ((∀ i k, k ∉ S.J i → P₀ i k = 0) → Stable S (bestResponse S Pstar) Pstar) := by sorry

end IncentiveFinNet.Supplement
