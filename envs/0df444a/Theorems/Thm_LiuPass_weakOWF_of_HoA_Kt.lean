-- Prove2me | Theorems.Thm_LiuPass_weakOWF_of_HoA_Kt
-- name    : LiuPass.weakOWF_of_HoA_Kt
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-20T22:29:50.642968+00:00
-- url     : https://prove2.me/theorems/69e7c2e5-7c4a-4a80-af49-62864ce4dbbe
-- title:
--   Theorem 4.1: one-way functions from mild average-case hardness of $K^t$
-- statement:
--   Theorem 4.1 of the paper, the direction "hardness of $K^{\mathrm{poly}}$ implies one-way
--   functions". Suppose there are polynomials $t > 0$ and $p > 0$ such that $K^t$ is
--   $\frac{1}{p}$-hard-on-average: every PPT heuristic computes $K^t(x)$ correctly on a uniformly
--   random $n$-bit $x$ with probability less than $1 - 1/p(n)$, for all sufficiently large $n$. Then
--   a weak one-way function exists.
--
--   The witness in the paper is
--   $$f(\ell \| \Pi') \;=\; \ell \,\|\, U(\Pi, 1^{t(n)}),$$
--   where $\ell$ is a string of length $\lceil \log(n+c)\rceil$, $\Pi'$ has length $n + c$, $\Pi$ is
--   the $\ell$-bit prefix of $\Pi'$, and $c$ is the constant of Fact 2.1; $f$ is shown to be
--   $\frac{1}{q}$-weak one-way for $q(n) = 2^{2c+3} n\, p(n)^2$. Combined with Yao's amplification
--   theorem this yields a one-way function.
-- source:
--   Yanyi Liu, Rafael Pass, On One-way Functions and Kolmogorov Complexity, arXiv:2009.11514v1 (FOCS 2020), https://arxiv.org/abs/2009.11514, p. 10, Theorem 4.1

import Definitions.Def_LiuPass_crypto
open Finset
open scoped Classical

namespace LiuPass

open Finset
open scoped Classical

theorem weakOWF_of_HoA_Kt (U : UMachine) (t p : ℕ → ℕ) (ht : IsPoly t) (htpos : ∀ n, 0 < t n)
    (hp : IsPoly p) (hppos : ∀ n, 0 < p n) (hhard : HoA U (fun n => 1 / (p n : ℝ)) (Kt U t)) :
    ∃ f : BitStr → BitStr, IsWeakOWF U f := by sorry
end LiuPass
