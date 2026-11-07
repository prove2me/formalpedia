-- Prove2me | Theorems.Thm_LowAccLTC_claim_5_9_good_partitions
-- name    : LowAccLTC.claim_5_9_good_partitions
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:09.097303+00:00
-- url     : https://prove2.me/theorems/2009f68d-defe-47f6-8865-109be4f13ae7
-- title:
--   Claim 5.9 — at least a $(1-28j^2/r)$-fraction of even partitions are good ($\ge0.99$ in §5.2's parameters)
-- statement:
--   Let $0<j$, $j\mid r$ and $k=r/j$.
--   1. At least a $(1-28j^2/r)$-fraction of the even partitions $\mathcal P:[r]\to[k]$ (blocks of size $j$) are good: $\mathcal P^{-1}(\{a,b\})$ contains no four cyclically consecutive colours for any blocks $a\neq b$.
--   2. In the parameters of §5.2 — $0<\varepsilon<1/2$, $r\ge10^{2765}\varepsilon^{-1095}\log^{182}(1/\varepsilon)$, $j=\lceil10^{15}\varepsilon^{-6}\log(1/\varepsilon)\rceil$, $j\mid r$ — this fraction is at least $0.99$.
--
--   Together with the colour-restriction Lemma 5.4, this reduces agreement testability of KMS codes to good partitions.
--
--   Differences from the source:
--   - generalization: 'in our parameters' (all of §5.2: bounds on r, p, d) → only 0 < ε < 1/2, the bound on r, j = ⌈10^15 ε^{-6} log(1/ε)⌉ and j ∣ r; reason: the bounds on p and d play no role; dropping them gives a statement that specializes to the source's
--   - encoding: the fraction of even partitions that are good → (1 − 28j²/r)·#even ≤ #good (and 0.99·#even ≤ #good); reason: equivalent since the set of even partitions is nonempty when j ∣ r
--   - encoding: colours i, i+1, i+2, i+3 modulo r → cyc i n = ⟨(i + n) mod r⟩ on Fin r; reason: colours are Fin r
--   - reading: log (base not stated) → Real.log (natural logarithm); reason: the paper does not fix the base; ln is the analyst's default and, as a lower-bound hypothesis, weaker than log₂ (ln x < log₂ x for x > 1)
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Claim 5.9, p.47 (PDF p.50)

import Definitions.Def_LowAccLTC_colorRestrict
import Definitions.Def_LowAccLTC_kmsParams

namespace LowAccLTC

/-- **Claim 5.9** (Most even partitions are good; Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.47 = PDF p.50).

1. For `0 < j`, `j ∣ r`, `k = r/j`, at least a `(1 - 28j²/r)`-fraction of the even partitions
`P : [r] → [k]` are good.
2. In the parameters of §5.2 (`0 < ε < 1/2`, `r ≥ 10^2765 ε^{-1095} log^182(1/ε)`,
`j = ⌈10^15 ε^{-6} log(1/ε)⌉`, `j ∣ r`), this fraction is at least `0.99`. -/
theorem claim_5_9_good_partitions :
    (∀ r j : ℕ, 0 < r → 0 < j → j ∣ r →
      (1 - 28 * (j : ℝ) ^ 2 / r) * ((evenPartitions r j (r / j)).card : ℝ) ≤
        ({P | P ∈ evenPartitions r j (r / j) ∧ IsGoodPartition P}.ncard : ℝ)) ∧
    (∀ (ε : ℝ) (r : ℕ), 0 < ε → ε < 1 / 2 →
      (10 : ℝ) ^ 2765 * ε ^ (-1095 : ℤ) * (Real.log (1 / ε)) ^ 182 ≤ r → kmsJ ε ∣ r →
      (0.99 : ℝ) * ((evenPartitions r (kmsJ ε) (r / kmsJ ε)).card : ℝ) ≤
        ({P | P ∈ evenPartitions r (kmsJ ε) (r / kmsJ ε) ∧ IsGoodPartition P}.ncard : ℝ)) := by sorry

end LowAccLTC
