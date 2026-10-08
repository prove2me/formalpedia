-- Prove2me | Theorems.Thm_KingmanSubadditive_Ulam_eq_2_4_7
-- name    : KingmanSubadditive.Ulam.eq_2_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:46:08.997337+00:00
-- url     : https://prove2.me/theorems/f2feefea-1361-4d22-b202-4edc57de8374
-- title:
--   (2.4.7) — P{l(π) ≥ r} ≤ (n choose k)[k! (r choose k)]⁻¹ for r ≥ k
-- statement:
--   Let $\pi$ be uniformly distributed over $\mathcal S_n$, let $k$ be a positive integer and let $r\ge k$ be an integer. Then
--   $$P\{l(\pi)\ge r\}\ \le\ \binom nk\Big[k!\binom rk\Big]^{-1}.$$
--
--   The bound is exact and holds for every $n$; letting $k$ and $r$ grow like multiples of $n^{1/2}$ gives the upper bound of Theorem 8.
--
--   **Formalization Note** $P$ is the proportion of the $n!$ permutations. Since $r\ge k$, $\binom rk\ge1$, so the right side involves no division by zero.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 896, §2.4, proof of Theorem 8, (2.4.7)

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

namespace KingmanSubadditive.Ulam

/-- **(2.4.7)** (Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), §2.4,
proof of Theorem 8, p. 896). For `π` uniform on `𝒮_n`, every positive integer `k` and every
`r ≥ k`, `P{l(π) ≥ r} ≤ (n choose k)[k! (r choose k)]⁻¹`.

**Formalization Note** `k` is positive, as in the paper ("let `k` be any positive integer");
`r ≥ k` makes `(r choose k) ≥ 1`, so the right side has no division by zero. The bound is exact
and holds for every `n`. -/
theorem eq_2_4_7 (n k r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    unifProb n (fun σ => r ≤ lis σ) ≤
      (n.choose k : ℝ) / ((Nat.factorial k : ℝ) * (r.choose k : ℝ)) := by sorry

end KingmanSubadditive.Ulam
