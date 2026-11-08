-- Prove2me | Theorems.Thm_MantriCVQ_theorem_1_7
-- name    : MantriCVQ.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:27.074459+00:00
-- url     : https://prove2.me/theorems/4e6a438f-b70b-4b76-830f-364c2482695b
-- title:
--   Theorem 1.7 — coupling bound for constant-depth circuits, Eq. (1.1)
-- statement:
--   Fix a code family of degree $d$, a depth $D$ and an exponent $A\ge1$. There are a constant $c>0$ and positive integers $h_0$, $n_0$, depending only on the code family, $D$ and $A$, such that the following holds for every $n\ge n_0$ and every $h$ with $h_0\le h\le h_{\max}(n)$. Let $F$ be a circuit on the leaves of an instance of size $n$ and height $h$, with AND and OR gates of unbounded fan-in and input negations, of depth at most $D$ and size at most $2^{n^A}$. For the coupled pair $(X_0,X_1)$ generated from the same random projections,
--   $$\Pr[F(X_0)\ne F(X_1)]\le2^{-cn},\qquad\bigl|\mathbb E_{\mu_{n,h,1}}F-\mathbb E_{\mu_{n,h,0}}F\bigr|\le2^{-cn}.$$
--   The two instances differ in a single leaf, and the theorem says no such circuit notices. This is the lower bound behind $L\notin\mathsf{PH}^O$.
--
--   Differences from the source:
--   - generalization: a code family of Definition 3.1 → any family with the degree condition (CodeDeg d); reason: the paper says the switching argument uses the code family only through the degree bound (p. 6); every code family of Definition 3.1 qualifies
--   - encoding: the expectation of F under the law of X_b → the probability over the seed that F(X_b) = 1; reason: F is Boolean and X_b is the pushforward of the uniform seed
--   - encoding: a circuit, size = gates and wires → a list of gates reading literals, constants and earlier gates, size = gates + total fan-in; reason: the same circuits and the same measure
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 1.7, Eq. (1.1), p. 5 (PDF p. 7)

import Mathlib
import Definitions.Def_MantriCVQ_ACCircuit
import Definitions.Def_MantriCVQ_CodeDeg
import Definitions.Def_MantriCVQ_Pr
import Definitions.Def_MantriCVQ_Seed
import Definitions.Def_MantriCVQ_dimsRange

open QAlgorithms.Complexity

namespace MantriCVQ

/-- **Theorem 1.7** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 1.7, Eq. (1.1), p. 5 (PDF p. 7)): fix a code family of degree `d`, a depth `D`
and an exponent `A ≥ 1`. There are `c > 0` and positive integers `h₀`, `n₀` such that for every `n ≥ n₀`, every
`h₀ ≤ h ≤ h_max(n)` and every circuit `F` on the leaves of an instance of size `n` and height `h` of depth at
most `D` and size at most `2^{n^A}`, the coupled pair satisfies `Pr[F(X₀) ≠ F(X₁)] ≤ 2^{-cn}`, and
`|E_{μ_{n,h,1}} F - E_{μ_{n,h,0}} F| ≤ 2^{-cn}`.

**Formalization Note** The pair `(X₀, X₁)` is `gen` from the same uniform seed. The expectation of the
Boolean `F` under `μ_{n,h,b}` is the probability that `F(X_b) = 1`. Size is gates plus wires, and `F` is
evaluated on every leaf table of the generated law. Only the degree bound of the code family is used. -/
theorem theorem_1_7 {d : ℕ} (C : CodeDeg d) (D : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ (c : ℝ) (h₀ n₀ : ℕ), 0 < c ∧ 0 < h₀ ∧ 0 < n₀ ∧
      ∀ n h : ℕ, n₀ ≤ n → h₀ ≤ h → h ≤ hmax n →
      ∀ F : ACCircuit (Addr (dimsRange n 0 h)), F.depth ≤ D →
        (F.size : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ A) →
        Pr (fun s : Seed (dimsRange n 0 h) =>
            F.eval (gen C.code _ s false) ≠ F.eval (gen C.code _ s true)) ≤
          (2 : ℝ) ^ (-(c * n)) ∧
        |Pr (fun s : Seed (dimsRange n 0 h) => F.eval (gen C.code _ s true) = true) -
            Pr (fun s : Seed (dimsRange n 0 h) => F.eval (gen C.code _ s false) = true)| ≤
          (2 : ℝ) ^ (-(c * n)) := by sorry

end MantriCVQ
