-- Prove2me | Theorems.Thm_HardyFiveAxioms_strictMono_completelyMultiplicative_eq_rpow
-- name    : HardyFiveAxioms.strictMono_completelyMultiplicative_eq_rpow
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T13:25:18.919982+00:00
-- url     : https://prove2.me/theorems/420e9f17-61c7-4864-a703-b80aaf53c19f
-- title:
--   Strictly increasing completely multiplicative functions are powers $n^\alpha$
-- statement:
--   Let $K$ be a real-valued function on the positive integers that is strictly increasing ($K(m)<K(n)$ whenever $1\le m<n$) and completely multiplicative ($K(mn)=K(m)K(n)$ for all $m,n\ge1$). Then there is a real $\alpha>0$ such that
--
--   $$K(n)=n^\alpha\qquad\text{for all }n\ge1 .$$
--
--   This is the number-theoretic input of Hardy's proof that $K=N^r$.
--
--   **Formalization Note** $K$ is a function `ℕ → ℝ`, constrained only on arguments $\ge1$, and $n^\alpha$ is the real power `Real.rpow`. The paper notes $\alpha>0$ in the course of the proof, and the statement includes it in the conclusion.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, pp. 29–30, Appendix 2, Eqs. (118)–(128)

import Mathlib

namespace HardyFiveAxioms

/-- Hardy 2001, Appendix 2: a strictly increasing, completely multiplicative function on the
positive integers is of the form `K(n) = n^α` (with `α > 0`). -/
theorem strictMono_completelyMultiplicative_eq_rpow (K : ℕ → ℝ)
    (hmono : ∀ m n : ℕ, 1 ≤ m → m < n → K m < K n)
    (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → K (m * n) = K m * K n) :
    ∃ α : ℝ, 0 < α ∧ ∀ n : ℕ, 1 ≤ n → K n = (n : ℝ) ^ α := by sorry

end HardyFiveAxioms
