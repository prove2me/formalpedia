-- Prove2me | Theorems.Thm_LL_Linnik491_modulus_over_totient491
-- name    : LL_Linnik491.modulus_over_totient491
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-25T04:00:59.421804+00:00
-- url     : https://prove2.me/theorems/43cf733c-fb6d-587b-b33a-c6c9c247d772
-- title:
--   $q\le D\,\varphi(q)\sqrt{\log N}$ for $q\le N^{1/10}$
-- statement:
--   There exist a real $D>0$ and a natural number $N_0$ such that for every natural number $N>N_0$ and every natural number $q$ with $1\le q$ and $q\le N^{1/10}$, the inequality $q\le D\,\varphi(q)\sqrt{\log N}$ holds, where $\varphi$ is Euler's totient and $\log$ the natural logarithm.
-- source:
--   Equation 5.5 in the Lean Lab reconstruction of Yu. V. Linnik, Prime numbers and powers of two, Trudy Mat. Inst. Steklov 38, 1951.

import Mathlib

namespace LL_Linnik491
theorem modulus_over_totient491 :
    ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        (q : ℝ) ≤ D * (q.totient : ℝ) * Real.sqrt (Real.log N) := by sorry
end LL_Linnik491
