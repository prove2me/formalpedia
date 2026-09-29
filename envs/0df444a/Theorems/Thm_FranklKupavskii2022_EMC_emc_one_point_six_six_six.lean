-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_emc_one_point_six_six_six
-- name    : FranklKupavskii2022.EMC.emc_one_point_six_six_six
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:23:28.999348+00:00
-- url     : https://prove2.me/theorems/793d7b91-8b69-4caf-a2fb-37292bdbf09f
-- title:
--   Theorem 14: the EMC for $n\ge s+(1.666+\varepsilon)s(k-1)$ and $s\ge s_0(\varepsilon)$
-- statement:
--   For every $\varepsilon>0$ there is $s_0=s_0(\varepsilon)$ such that for all $s\ge s_0$, all $k\ge1$ and all $n$ with
--
--   $$
--   n\ge s+(1.666+\varepsilon)s(k-1)
--   $$
--
--   we have
--
--   $$
--   m(n,k,s)=\binom nk-\binom{n-s}k. \tag{6}
--   $$
--
--   This is the form of the main result that the paper proves, by induction on $k$; Theorem 1 follows by taking $\varepsilon<5/3-1.666$. The threshold $s_0$ does not depend on $k$ or $n$.
--
--   **Formalization Note** $1.666$ is the exact decimal. The Sect. 1 assumption $n\ge k(s+1)$ is not needed as a hypothesis: it follows from the threshold for $k,s\ge2$, and for $k=1$ (6) holds for all $n\ge s$.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Theorem 14, p. 9

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_emcMax

namespace FranklKupavskii2022.EMC

/-- Theorem 14 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 9): for any `ε > 0` there exists
`s_0 = s_0(ε)` such that for any `s ≥ s_0` and `n ≥ s + (1.666 + ε)s(k − 1)` the conclusion of
Theorem 1 is valid, i.e. `m(n, k, s) = \binom{n}{k} − \binom{n−s}{k}` (6).

**Formalization Note.** `1.666` is the exact decimal `1666/1000`. `s_0` depends on `ε` only, and
is chosen before `k` and `n`. `k ≥ 1` is the standing "positive integers" assumption (at `k = 0`,
(6) fails). The Sect. 1 assumption `n ≥ k(s + 1)` is not a binder: it follows from the threshold
for `k ≥ 2` and `s ≥ 2`, and at `k = 1` (6) holds for every `n ≥ s`. The natural subtraction is
exact. -/
theorem emc_one_point_six_six_six (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ,
      (s : ℝ) + (1666 / 1000 + ε) * s * ((k : ℝ) - 1) ≤ n →
      emcMax n k s = n.choose k - (n - s).choose k := by sorry

end FranklKupavskii2022.EMC
