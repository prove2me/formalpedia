-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_exponential_upper_bound
-- name    : KawasakiSOS.Threshold.exponential_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:06:27.389572+00:00
-- url     : https://prove2.me/theorems/3ec970e0-8c10-456e-b1ad-5da09ffdd4ee
-- title:
--   Remark 3.3: exponential upper bound
-- statement:
--   For $\lambda>1$, $2\le k\le n$ and $\varepsilon\in(0,1)$, the lazy Kawasaki chain satisfies
--
--   $$\tau(\varepsilon)\le4k|\Omega|^2\lambda^{2n}\Bigl(\log|\Omega|+2n\log\lambda+\log\frac1\varepsilon\Bigr),$$
--
--   where $|\Omega|\le(n+1)^{k-1}$. For fixed $k$ this shows that the mixing time is at most exponential in $n$, and it supplies the upper bound in clause (i) of the goal theorem.
--
--   Differences from the source:
--   - reading: "For fixed k and λ > 1" → the display for all 2 ≤ k ≤ n, with k explicit; reason: "fixed k" belongs to the exponential conclusion; the derivation and the display hold for each k, and the k-dependence is written out
--   - reading: τ(ε) with ε unrestricted → ε in (0,1); reason: the range of Theorem 1.2
--   - encoding: τ(ε) is the least t with d(t) ≤ ε → a conjunct also asserts that {t | d(t) ≤ ε} is nonempty; reason: Lean's sInf on ℕ is 0 on the empty set, so without the conjunct an upper bound could hold for free
--   - reading: "its mixing time" → the worst-case total variation mixing time of the lazy chain; reason: the source does not define the term; this is the standard meaning, as in its reference [LPW17]
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Remark 3.3, p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_tau
import Definitions.Def_KawasakiSOS_Threshold_mixingSet

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Remark 3.3, p. 9 (PDF p. 10).

Formalization Notes:
- reading: "For fixed k and λ > 1" → the display for all 2 ≤ k ≤ n, with k explicit. "fixed k" belongs to the exponential conclusion; the derivation and the display hold for each k, and the k-dependence is written out.
- reading: τ(ε) with ε unrestricted → ε in (0,1). The range of Theorem 1.2.
- encoding: τ(ε) is the least t with d(t) ≤ ε → a conjunct also asserts that {t | d(t) ≤ ε} is nonempty. Lean's sInf on ℕ is 0 on the empty set, so without the conjunct an upper bound could hold for free.
- reading: "its mixing time" → the worst-case total variation mixing time of the lazy chain. The source does not define the term; this is the standard meaning, as in its reference [LPW17]. -/
theorem exponential_upper_bound {n k : ℕ} [NeZero k] (hk : 2 ≤ k) (hkn : k ≤ n) {lam : ℝ} (hlam : 1 < lam) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    (mixingSet n k lam ε).Nonempty ∧
      (tau n k lam ε : ℝ) ≤ 4 * (k : ℝ) * (Fintype.card (Config n k) : ℝ) ^ 2 * lam ^ (2 * n) *
        (Real.log (Fintype.card (Config n k) : ℝ) + 2 * (n : ℝ) * Real.log lam + Real.log (1 / ε)) ∧
      Fintype.card (Config n k) ≤ (n + 1) ^ (k - 1) := by sorry

end KawasakiSOS.Threshold
