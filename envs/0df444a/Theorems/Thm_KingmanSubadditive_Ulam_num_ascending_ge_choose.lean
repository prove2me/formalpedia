-- Prove2me | Theorems.Thm_KingmanSubadditive_Ulam_num_ascending_ge_choose
-- name    : KingmanSubadditive.Ulam.num_ascending_ge_choose
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:46:13.872402+00:00
-- url     : https://prove2.me/theorems/bcbbb883-c470-439b-82fc-6860413e91ca
-- title:
--   Proof of Theorem 8, p. 896 — if l(π) ≥ k then ν ≥ (l(π) choose k)
-- statement:
--   Let $\sigma\in\mathcal S_n$ and let $k$ be an integer with $l(\sigma)\ge k$. Then the number $\nu$ of ascending sequences of length $k$ in $\sigma$ satisfies
--   $$\nu\ \ge\ \binom{l(\sigma)}{k}.$$
--
--   Every $k$-element subsequence of a longest ascending sequence is itself ascending; this deterministic inequality converts the first moment of $\nu$ into the tail bound (2.4.7).
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 896, §2.4, proof of Theorem 8

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

namespace KingmanSubadditive.Ulam

/-- (Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), §2.4, proof of
Theorem 8, p. 896.) If `l(π) ≥ k`, there is an ascending sequence of length `l(π)`, and each of its
subsequences of length `k` is ascending, so `ν ≥ (l(π) choose k)`, where `ν` is the number of
ascending sequences of length `k` in `π`. The statement is deterministic: it holds for every
permutation `σ ∈ 𝒮_n`. -/
theorem num_ascending_ge_choose {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ lis σ) :
    (lis σ).choose k ≤ numAscending k σ := by sorry

end KingmanSubadditive.Ulam
