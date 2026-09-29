-- Prove2me | Theorems.Thm_LiuPass_owf_iff_Kt_mildly_HoA
-- name    : LiuPass.owf_iff_Kt_mildly_HoA
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-20T22:41:41.065271+00:00
-- url     : https://prove2.me/theorems/245953ad-ea2f-428a-8f8c-d1d896b7a055
-- title:
--   Theorem 3.1: one-way functions exist iff $K^{\mathrm{poly}}$ is mildly hard-on-average
-- statement:
--   The main theorem of the paper (Theorem 3.1, restated as Theorem 1.1): the following are
--   equivalent.
--
--   **(a)** One-way functions exist.
--
--   **(b)** There exists a polynomial $t(n) > 0$ such that $K^t$ is mildly hard-on-average: for some
--   positive polynomial $p$, every PPT heuristic $H$ satisfies
--   $\Pr[x \leftarrow \{0,1\}^n : H(x) = K^t(x)] < 1 - 1/p(n)$ for all sufficiently large $n$.
--
--   **(c)** For all constants $d > 0$ and $\varepsilon > 0$ and every polynomial
--   $t(n) \ge (1+\varepsilon)n$, the function $K^t$ is mildly hard-on-average to
--   $(d\log n)$-approximate.
--
--   Equivalently: secure private-key encryption, digital signatures, pseudorandom generators,
--   pseudorandom functions and commitment schemes are possible **if and only if** computing the
--   time-bounded Kolmogorov complexity of a uniformly random string is mildly hard on average. The
--   implication (b) $\Rightarrow$ (a) is Theorem 4.1 followed by Yao's amplification; (a)
--   $\Rightarrow$ (c) is Theorem 5.6 followed by Theorem 5.2; (c) $\Rightarrow$ (b) is immediate,
--   since exact computation is at least as hard as approximation.
-- source:
--   Yanyi Liu, Rafael Pass, On One-way Functions and Kolmogorov Complexity, arXiv:2009.11514v1 (FOCS 2020), https://arxiv.org/abs/2009.11514, p. 9, Theorem 3.1 (= Theorem 1.1, p. 2)

import Definitions.Def_LiuPass_crypto
open Finset
open scoped Classical

namespace LiuPass

open Finset
open scoped Classical

theorem owf_iff_Kt_mildly_HoA (U : UMachine) :
    ((∃ f : BitStr → BitStr, IsOWF U f) ↔
        ∃ t : ℕ → ℕ, IsPoly t ∧ (∀ n, 0 < t n) ∧ MildlyHoA U (Kt U t)) ∧
      ((∃ f : BitStr → BitStr, IsOWF U f) ↔
        ∀ d : ℕ, 0 < d → ∀ eps : ℝ, 0 < eps → ∀ t : ℕ → ℕ, IsPoly t →
          (∀ n : ℕ, (1 + eps) * (n : ℝ) ≤ (t n : ℝ)) →
            MildlyHoAApprox U (fun n => d * Nat.log 2 n) (Kt U t)) := by sorry
end LiuPass
