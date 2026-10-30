-- Prove2me | Theorems.Thm_LearnDoFrontier_TwoAction_eq18_general_solution
-- name    : LearnDoFrontier.TwoAction.eq18_general_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:46.251487+00:00
-- url     : https://prove2.me/theorems/fdbf8240-dd99-4f50-ae60-b2aabeb60ad7
-- title:
--   §4.3, Eq. (18), p. 21 — general solution of a linear recurrence with repeated characteristic roots
-- statement:
--   Let $n \ge 0$ and $q_1, \dots, q_n \in \mathbb C$, and consider the homogeneous linear difference equation (16)
--   $$x(k+n) + q_1 x(k+n-1) + \cdots + q_n x(k) = 0, \qquad k = 0, 1, 2, \dots$$
--   Suppose its characteristic polynomial factors as $z^n + q_1 z^{n-1} + \cdots + q_n = \prod_{i=1}^r (z - z_i)^{m_i}$ with distinct $z_1, \dots, z_r \in \mathbb C$ and multiplicities $m_i \ge 1$ (so $\sum_i m_i = n$). Then a sequence $x : \mathbb N \to \mathbb C$ solves (16) if and only if there are coefficients $a_{i,\tau} \in \mathbb C$ ($1 \le i \le r$, $0 \le \tau \le m_i - 1$) with
--   $$x(k) = \sum_{i=1}^r \sum_{\tau=0}^{m_i-1} a_{i,\tau} \binom{k}{\tau} z_i^{k-\tau} \qquad \text{for all } k \ge 0,$$
--   with the convention $\binom{k}{\tau} = 0$ for $k < \tau$.
--
--   This is the classical description of the solution space of (16), in the binomial form the paper uses for Theorem 6. It covers both of the paper's cases, distinct roots ($r = n$) and repeated roots.
--
--   **Formalization Note** The statement is over $\mathbb C$ and the roots are given as an injective family with the factorization of the characteristic polynomial as a hypothesis. Natural-number subtraction in the exponent $k - \tau$ is harmless because the binomial coefficient vanishes when $k < \tau$.
-- source:
--   Zhang, SSRN 3847049 (accepted version with E-Companion), pp. 20–21, §4.3, Eqs. (16)–(18), case (2)

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra

open Polynomial

namespace LearnDoFrontier.TwoAction

theorem eq18_general_solution (n : ℕ) (q : Fin n → ℂ) (r : ℕ) (z : Fin r → ℂ) (m : Fin r → ℕ)
    (hz : Function.Injective z) (hm : ∀ i, 1 ≤ m i)
    (hchar : charPoly n q = ∏ i : Fin r, (X - C (z i)) ^ (m i)) (x : ℕ → ℂ) :
    recSol n q x ↔ ∃ a : (Σ i : Fin r, Fin (m i)) → ℂ, ∀ k : ℕ, x k = rootExp z m a k := by sorry

end LearnDoFrontier.TwoAction
