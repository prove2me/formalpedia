-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_Supplement_classical_tester
-- name    : FourierDimTesting102.Quantum.Supplement.classical_tester
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:29:42.892052+00:00
-- url     : https://prove2.me/theorems/a7246d09-dcb3-454c-ad60-d608223060df
-- title:
--   Theorem 4.1 — Algorithm 2 tests Fourier dimension with $O(2^{k/2}k/\epsilon)$ classical queries
-- statement:
--   Let $\epsilon>0$. Algorithm 2 (with the parameters fixed in the Algorithms definition) makes at most
--
--   $$
--   C\,(k+1)\,\frac{2^{k/2}}{\epsilon}
--   $$
--
--   classical queries to $f:\mathbb F_2^n\to\{-1,1\}$, for an absolute constant $C$ independent of $n,k,\epsilon$; for $k\ge1$ this is at most $2C\cdot2^{k/2}k/\epsilon=\tilde O(2^{k/2}/\epsilon)$. Moreover, for every $f$:
--
--   1. if $f$ has Fourier dimension at most $k$, Algorithm 2 accepts with probability at least $2/3$;
--   2. if $\operatorname{dist}(f,D_k)\ge\epsilon$, Algorithm 2 rejects with probability at least $2/3$.
--
--   This is the classical counterpart of Theorem 3.1: up to lower-order factors it matches the classical lower bound of Gopalan et al., and together with Theorem 3.1 it exhibits the exponential quantum advantage in $k$.
--
--   Differences from the source:
--   - encoding: boolean functions f : F₂ⁿ → {−1,1} → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x} (the base Model); reason: a bijection on the same functions; the bit is what the oracle returns
--   - encoding: classical query access: query x, obtain f(x) (§2.2) → a NonadaptiveRandAlg: a uniform seed fixes all query points, the output is computed from the seed and the answers; the query count is the number of query indices; reason: the algorithm in question is nonadaptive; repeated points are counted, so the count is the source’s worst-case count
--   - reading: Algorithm 2 with T = O(1), m = O(k/ϵ), ℓ = O(2^{k/2}), “by adjusting the constant inside” → alg2 with T = 1000, m = ⌈(k ln 2 + ln 100)/ε⌉, ℓ the least integer with C(ℓ,2) ≥ 2^{k−1}; λ and τ as printed; reason: the source leaves these constants open; the chosen ones give λ ∈ [1/2,1], e^{−εm} ≤ 0.01·2^{−k} and Hoeffding error below 1/3, as the proof requires
--   - reading: Algorithm 2 for every fixed ϵ > 0 → for ε > 1/2 the algorithm runs no rounds and accepts with zero queries; reason: no function is at distance above 1/2 from both constants, so there is no no-instance; for ε ≤ 1/2 the algorithm is the printed one
--   - generalization: O(2^{k/2}k/ϵ) queries (0 at k = 0) → at most C(k+1)2^{k/2}/ε queries for every k ≥ 0, one absolute C; reason: for k ≥ 1, k + 1 ≤ 2k gives the source’s bound with constant 2C; the bound also covers k = 0 and is uniform in ε
--   - reading: ϵ-far from having Fourier dimension k → distToSet f (Dk n k) ≥ ε, with D_k the functions of Fourier dimension at most k; reason: p.13 and Definition 2.6 use “dimension k” for “at most k” and “far” for distance at least ϵ; the base goal reads it the same way
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.19, Theorem 4.1 (Algorithm 2, p.19; proof pp.20–23 with Lemmas 4.1–4.4)

import Definitions.Def_FourierDimTesting102_Quantum_Supplement_Algorithms

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-- Theorem 4.1, p.19: there is an absolute constant `C` such that for every `n`, `k` and `ε > 0`,
Algorithm 2 (`alg2 n k ε`, fixed before `f`) makes at most `C (k+1) 2^{k/2}/ε` classical queries,
accepts (`true`) every `f` of Fourier dimension at most `k` with probability at least `2/3`, and
rejects (`false`) every `f` with `dist(f, D_k) ≥ ε` with probability at least `2/3`. For `k ≥ 1`
the bound is at most `2C · 2^{k/2} k/ε`. -/
theorem classical_tester :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) (ε : ℝ), 0 < ε →
      ((alg2 n k ε).queries : ℝ) ≤ C * ((k : ℝ) + 1) * (2 : ℝ) ^ ((k : ℝ) / 2) / ε ∧
      ∀ f : BoolFn n,
        (fourierDim f ≤ k → 2 / 3 ≤ (alg2 n k ε).outProb f true) ∧
        (ε ≤ distToSet f (Dk n k) → 2 / 3 ≤ (alg2 n k ε).outProb f false) := by sorry

end FourierDimTesting102.Quantum.Supplement
