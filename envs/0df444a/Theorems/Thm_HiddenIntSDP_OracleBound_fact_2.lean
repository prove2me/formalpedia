-- Prove2me | Theorems.Thm_HiddenIntSDP_OracleBound_fact_2
-- name    : HiddenIntSDP.OracleBound.fact_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:43.709103+00:00
-- url     : https://prove2.me/theorems/927ca2eb-124e-403e-b253-bb4040c07281
-- title:
--   Fact 2, p. 17 — structure of the SDP error matrix
-- statement:
--   Let $B=Y-Y^*$ for a feasible SDP matrix $Y$ under a balanced mixture model. Then $B$ has zero diagonal, entries in $[-1,0]$ within true clusters and in $[0,1]$ between clusters, and zero row sums. Summing by true cluster gives the corresponding zero block-row sums. The entrywise error $\gamma=\|B\|_1$ satisfies
--
--   $$
--   \gamma=\sum_{\sigma^*(i)\ne\sigma^*(j)}B_{ij}
--          -\sum_{\sigma^*(i)=\sigma^*(j)}B_{ij},
--   \qquad
--   \frac\gamma2=\sum_{\sigma^*(i)\ne\sigma^*(j)}B_{ij}
--                =-\sum_{\sigma^*(i)=\sigma^*(j)}B_{ij}.
--   $$
--
--   The six clauses supply the structural identities used throughout Section 5.
-- source:
--   Fei & Chen, Hidden integrality and semi-random robustness of SDP relaxation for sub-Gaussian mixture model, arXiv:1803.06510v2, p. 17, Fact 2(a)–(f)

import Definitions.Def_HiddenIntSDP_OracleBound_Proof

namespace HiddenIntSDP.OracleBound

/-- Fei–Chen, Fact 2(a)–(f), p. 17, for the error matrix `B = Y - Ystar sig`. -/
theorem fact_2 {n k : ℕ} (hn : 4 ≤ n) (hk : 2 ≤ k)
    (sig : Fin n → Fin k) (hbal : Balanced n k sig)
    (Y : Matrix (Fin n) (Fin n) ℝ) (hY : SDPFeasible n k Y) :
    let B := Y - Ystar sig
    (∀ i, B i i = 0) ∧
    (∀ i j, (sig i = sig j → -1 ≤ B i j ∧ B i j ≤ 0) ∧
      (sig i ≠ sig j → 0 ≤ B i j ∧ B i j ≤ 1)) ∧
    (∀ i, (∑ j ∈ Finset.univ.filter (fun j => sig j ≠ sig i), B i j) =
      -(∑ j ∈ Finset.univ.filter (fun j => sig j = sig i), B i j)) ∧
    (∀ a, (∑ i ∈ Finset.univ.filter (fun i => sig i = a),
      ∑ j ∈ Finset.univ.filter (fun j => sig j ≠ a), B i j) =
      -(∑ i ∈ Finset.univ.filter (fun i => sig i = a),
        ∑ j ∈ Finset.univ.filter (fun j => sig j = a), B i j)) ∧
    gamma sig Y =
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j => sig i ≠ sig j), B i j) -
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j => sig i = sig j), B i j) ∧
    gamma sig Y / 2 =
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j => sig i ≠ sig j), B i j) ∧
    gamma sig Y / 2 =
      -(∑ i, ∑ j ∈ Finset.univ.filter (fun j => sig i = sig j), B i j) := by sorry

end HiddenIntSDP.OracleBound
