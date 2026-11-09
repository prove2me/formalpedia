-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_quantum_fourier_dimension_tester
-- name    : FourierDimTesting102.Quantum.quantum_fourier_dimension_tester
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:06:59.707024+00:00
-- url     : https://prove2.me/theorems/3d2a92ef-3a9f-4390-b17c-71d0c0c49d1b
-- title:
--   Theorem 3.1: a one-sided quantum tester for Fourier dimension with $O(k/\sqrt\epsilon)$ queries
-- statement:
--   Fix natural numbers $n,k$ and a real $\epsilon>0$, and let $\mathcal T=\mathcal T_{n,k,\epsilon}$ be Algorithm 1, a quantum algorithm fixed before the input that accesses a boolean function $f:\mathbb F_2^n\to\{-1,1\}$ only through the XOR oracle $O_f$. Then:
--
--   1. On every branch, $\mathcal T$ makes at most $448(k+1)/\sqrt\epsilon$ queries, hence at most $896k/\sqrt\epsilon$ queries when $k\ge1$. In particular it uses $O(k/\sqrt\epsilon)$ queries, with absolute constants independent of $n,k,\epsilon,f$.
--   2. If $f$ has Fourier dimension at most $k$, then $\mathcal T$ accepts with probability $1$.
--   3. If $\operatorname{dist}(f,D_k)\ge\epsilon$, then $\mathcal T$ rejects with probability at least $2/3$.
--
--   $$
--   \Pr[\mathcal T^{f}\text{ accepts}]=1\ \text{ if }\widehat{\dim}(f)\le k,\qquad
--   \Pr[\mathcal T^{f}\text{ rejects}]\ge\tfrac23\ \text{ if }\operatorname{dist}(f,D_k)\ge\epsilon.
--   $$
--
--   Since any classical tester needs $\Omega(2^{k/2})$ queries, this is the paper's exponential quantum advantage for a classically testable property.
--
--   **Formalization Note** `tester n k ε` is a published `AdaptiveQueryAlg` with output `true` for accept. Its gates and tree take no argument $f$, and the probabilities are those of the actual measured transcripts. The query bound is stated for `worstCaseQueries`, which counts all branches, and the theorem also records that it dominates the published `maxQueries` on each input.
--
--   Differences from the source:
--   - encoding: boolean functions f : {0,1}^n → {−1,1}, with frequencies written as subsets S ⊆ [n] or their indicator vectors → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x}, and frequencies are vectors of Fin n → ZMod 2; reason: a bijection on the same functions; the bit is what the XOR oracle adds and the vectors carry the F₂-subspaces
--   - encoding: quantum query oracle |x⟩|b⟩ → |x⟩|b ⊕ f(x)⟩ with sign-valued f → the published xorOracle of the bit function f; reason: the source XORs the bit of f; this is that bit
--   - encoding: uses O(k/√ϵ) quantum queries → every branch has at most 448(k+1)/√ε queries, and at most 896k/√ε for k ≥ 1; reason: explicit absolute constants imply the O-bound; 448 and 896 are this formalization’s constants, not printed in the paper
--   - generalization: the O(k/√ϵ) bound, which is 0 at k = 0 → the bound with k + 1 also covers k = 0, and the k ≥ 1 clause is the source’s bound; reason: k = 0 (constant functions) cannot be tested with zero queries; for k ≥ 1 the clause is the source’s O(k/√ϵ)
--   - reading: m = O(k) rounds and a hard cap of O(1/√ϵ) queries for amplitude amplification, with constants left adjustable → m = 64(k+1), L = ⌈2/√ε⌉, and per round j = 0 on a fair coin, otherwise j uniform on {0,…,L}, with 2j+1 queries; reason: the source leaves the schedule and constants open; the mass outside W is unknown, so the iterate count is randomized rather than tuned to f
--   - reading: Algorithm 1 for any ϵ > 0 (Definition 2.5 sets no upper bound on ϵ) → for ε > 1/2 the tester accepts at once with zero queries, and ε = 1/2 runs the loop; reason: no function is at distance above 1/2 from both constants, so there is no no-instance; every claim of the theorem holds for this branch
--   - reading: ϵ-far from having Fourier dimension k → distToSet f (Dk n k) ≥ ε, with D_k the functions of dimension at most k; reason: p.13 says “dimension k” abbreviates “at most k” in testing statements, and Definition 2.6 reads far as distance at least ϵ
--   - encoding: classical randomness of the tester → a zero-query round measuring a uniform workspace of size 2(L+1); reason: AdaptiveQueryAlg branches only on measurement outcomes; this round consults no oracle
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.14, Theorem 3.1 (informal Theorem 1.1, p.3)

import Definitions.Def_FourierDimTesting102_Quantum_Algorithm

namespace FourierDimTesting102.Quantum

open QAlgorithms

/-- Theorem 3.1, p.14: Algorithm 1 (`tester n k ε`, fixed before `f`) makes `O(k/√ε)` oracle
queries on every branch, with absolute constants, and it is a one-sided tester: it accepts with
probability `1` every `f` of Fourier dimension at most `k`, and rejects with probability at least
`2/3` every `f` at distance at least `ε` from `D_k`. Output `true` is accept. -/
theorem quantum_fourier_dimension_tester (n k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (worstCaseQueries (tester n k ε) : ℝ) ≤ 448 * ((k : ℝ) + 1) / Real.sqrt ε ∧
    (1 ≤ k → (worstCaseQueries (tester n k ε) : ℝ) ≤ 896 * (k : ℝ) / Real.sqrt ε) ∧
    ∀ f : BoolFn n,
      (tester n k ε).maxQueries f ≤ worstCaseQueries (tester n k ε) ∧
      (fourierDim f ≤ k → (tester n k ε).outProb f true = 1) ∧
      (ε ≤ distToSet f (Dk n k) → 2 / 3 ≤ (tester n k ε).outProb f false) := by sorry

end FourierDimTesting102.Quantum
