-- Prove2me | Theorems.Thm_KellyReversibility_Genetics_ewens_sum_eq_one
-- name    : KellyReversibility.Genetics.ewens_sum_eq_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:08:57.050477+00:00
-- url     : https://prove2.me/theorems/8eb26faf-7a0a-4228-b55e-ea74ef202204
-- title:
--   Exercise 7.1.3 — the Ewens distribution sums to unity
-- statement:
--   Let $\nu>0$ and $n\ge 2$. For every description $\mathbf M$ of a population of size $n$ (so $\sum_i iM_i=n$), the Ewens probability $\pi_n(\mathbf M)$ of (7.6) is positive, and
--
--   $$\sum_{\mathbf M:\ \sum_i iM_i=n}\ \binom{\nu+n-1}{n}^{-1}\prod_{i=1}^{n}\Big(\frac{\nu}{i}\Big)^{M_i}\frac{1}{M_i!}=1 .$$
--
--   So (7.6) is an equilibrium distribution in the sense of §1.1 (positive numbers summing to unity). The book leaves this to Exercise 7.1.3. It is needed to read Theorem 7.1 as a statement about probability distributions.
--
--   **Formalization Note** Descriptions are partitions of $n$ (`Nat.Partition n`, a finite type), so the sum is a finite sum.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 146, Eq. (7.6); normalization stated in Exercise 7.1.3, p. 148

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal
import Definitions.Def_KellyReversibility_Genetics_Ewens

namespace KellyReversibility.Genetics

/-- Kelly (1979), Eq. (7.6), p. 146 (and Exercise 7.1.3, p. 148): for `ν > 0` the Ewens
distribution on the descriptions of a population of size `n` is a probability distribution:
every description has positive probability and the probabilities sum to unity. -/
theorem ewens_sum_eq_one (ν : ℝ) (hν : 0 < ν) (n : ℕ) (hn : 2 ≤ n) :
    (∀ p : Nat.Partition n, 0 < ewens ν n p) ∧ ∑ p : Nat.Partition n, ewens ν n p = 1 := by sorry

end KellyReversibility.Genetics
