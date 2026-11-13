-- Prove2me | Theorems.Thm_MultiThinkCoT_runtime_F
-- name    : MultiThinkCoT.runtime_F
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:59.116257+00:00
-- url     : https://prove2.me/theorems/3d3624cc-d1bc-477d-bf5b-124aabca8b79
-- title:
--   Appendix F "Runtime" — Algorithm 1 runs in polynomial time
-- statement:
--   Consider Algorithm 1 with $K=\lceil8\log(2m)\rceil$. Suppose the oracle's cost on $N$ pairs of maximal length $n$ is at most $A(d+n+N+1)^a$, and one next-token evaluation on a string of length $\ell$ costs at most $B(d+\ell+1)^b$. Then there are $C,k$ depending only on $A,a,B,b$ such that for every $d$, $T$, $m\ge1$, $M_\star$ and $\delta\in(0,1)$, every oracle, every adversary and every training set with inputs of length at most $d$, every run together with one evaluation of its output on an input of length at most $d$ costs at most
--
--   $$
--   C\,\big(d+T+m+M_\star+\lceil\log\delta^{-1}\rceil+2\big)^k .
--   $$
--
--   This is the paper's statement that the total runtime is polynomial in $T$ and in the size $m$ of the training set when the base class has a tractable Consistent oracle. Decomposing each CoT into its prefix–next-token pairs is polynomial in $m$ and $T$.
--
--   **Formalization Note** The cost is the one accumulated line by line inside the definition of Algorithm 1: unit-cost real arithmetic, the oracle charged by its cost function, next-token evaluations charged by theirs. The bound also tracks $M_\star$ and $\lceil\log\delta^{-1}\rceil$, since for a general $m$ the batch size and the number of attempts depend on them. In Theorem 7 both are bounded polynomially.
--
--   Differences from the source:
--   - reading: the total runtime is polynomial in T and in m = m(ε, δ), given a tractable Consistent oracle → under the per-line cost model of alg1, every run plus one output evaluation costs ≤ C(d + T + m + M⋆ + ⌈log δ⁻¹⌉ + 2)^k for every m ≥ 1, M⋆, δ ∈ (0,1), with C, k depending only on the polynomial cost bounds; reason: the paper names no machine model; for general m the attempts ⌈log₂(2K/δ)⌉ depend on δ and the batches on M⋆, both polynomially bounded by m when m = m(ε, δ) and M⋆ = O(VCdim); d enters through Definition 1.1's poly(d, n, m)
--   - generalization: provided the base class has a tractable Consistent oracle → every oracle function (its cost is charged through the polynomially bounded oc) and every adversary strategy; reason: consistency of the oracle does not affect the charges; the paper's oracles are among these
--   - encoding: the runtime includes evaluating ĥ(x) on a new input x ∈ X_d (§6.1, p.17) → one evaluation of the output on any string of length ≤ d is added; reason: X_d ⊆ {0,1}^{≤d}
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix F, paragraph "Runtime", p.57 (PDF p.57)

import Mathlib
import Definitions.Def_MultiThinkCoT_alg1

namespace MultiThinkCoT

/-- **Appendix F, paragraph "Runtime"**, p.57 (PDF p.57).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

"The total runtime is polynomial in `T` and in the size `m` of the initial end-to-end training
set, provided that the base class has tractable Consistent oracle (Definition 1.1). Indeed, given
CoT samples, constructing a predictor consistent with them only requires decomposing each CoT into
all prefix–next-token pairs, which can be done in time polynomial in `m` and `T`."

Stated for Algorithm 1 with `K = ⌈8 log(2m)⌉`: for all polynomial bounds
`oc(n, N) ≤ A (d + n + N + 1)^a` on the oracle's cost on `N` pairs of maximal length `n` and
`ec(ℓ) ≤ B (d + ℓ + 1)^b` on the cost of one next-token evaluation on a string of length `ℓ`, there
are `C, k` such that every run on inputs of length at most `d`, plus one evaluation of its output
on an input of length at most `d`, costs at most `C (d + T + m + M⋆ + ⌈log δ⁻¹⌉ + 2)^k`.

**Formalization Note.**
* The cost is the one accumulated line by line inside `alg1` (unit-cost real arithmetic; see
  `MultiThinkCoT.alg1`). `C` and `k` depend only on `A, a, B, b`.
* The bound is for every `m ≥ 1` and every `M⋆`, so it is polynomial in `M⋆` and `⌈log δ⁻¹⌉`
  as well as in `d, T, m`: for general `m` the number of attempts `⌈log₂(2K/δ)⌉` depends on `δ`
  and the batch size on `M⋆`; in Theorem 7 (`m = m(ε, δ)`, `M⋆ = O(VCdim)`) both are polynomially
  bounded. `d` enters through Definition 1.1 (`poly(d, n, m)`) and the input lengths.
* The bound holds for every oracle and every adversary strategy (their choices do not change the
  charges beyond `oc` and `ec`).
-/
theorem runtime_F :
    ∀ A a B b : ℕ, ∃ C k : ℕ,
    ∀ (oc : ℕ → ℕ → ℕ) (ec : ℕ → ℕ) (d : ℕ),
      (∀ n N, oc n N ≤ A * (d + n + N + 1) ^ a) → (∀ l, ec l ≤ B * (d + l + 1) ^ b) →
      ∀ (T m Mst : ℕ) (δ : ℝ), 1 ≤ m → 0 < δ → δ < 1 →
      ∀ (O : List (List Bool × Bool) → Gen) (xs : Fin m → List Bool), (∀ i, (xs i).length ≤ d) →
      ∀ (ys : Fin m → Bool) (adv : History m → Finset (Fin m) → Gen),
      ∀ r ∈ (alg1 T O oc ec ⌈8 * Real.log (2 * m)⌉₊ Mst δ xs ys adv).support,
      ∀ x : List Bool, x.length ≤ d →
        r.cost + r.pred.evalCost ec T x ≤
          C * (d + T + m + Mst + ⌈Real.log (1 / δ)⌉₊ + 2) ^ k := by sorry

end MultiThinkCoT
