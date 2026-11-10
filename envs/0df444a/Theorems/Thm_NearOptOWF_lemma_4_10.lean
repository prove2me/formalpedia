-- Prove2me | Theorems.Thm_NearOptOWF_lemma_4_10
-- name    : NearOptOWF.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:50:42.908261+00:00
-- url     : https://prove2.me/theorems/8abb2c99-5ad9-4607-a9ca-65658464f0f4
-- title:
--   Lemma 4.10 — inverting random images of a PRF implies inverting uniform targets, up to $2^{\min\{n,m\}-m}/(nm)$
-- statement:
--   Let $K = \{f : \{0,1\}^n \to \{0,1\}^m\}$ be a sub-exponentially secure PRF. There are $c > 0$, an exponent $k_0$ and a threshold $n_0$ such that for all $n \ge n_0$, $m \ge 1$ and security parameters $\lambda \ge (n+m)^{k_0}$, every randomized algorithm $A$ and every real $\epsilon$: if
--   $$
--   \Pr_{f \leftarrow K,\ x \leftarrow \{0,1\}^n}\bigl[A(f, f(x)) = x' \wedge f(x') = f(x)\bigr] \ge \epsilon,
--   $$
--   then
--   $$
--   \Pr_{f \leftarrow K,\ y \leftarrow \{0,1\}^m}\bigl[A(f, y) = x' \wedge f(x') = y\bigr] \ge \frac{2^{\min\{n,m\}-m}}{nm}\,\epsilon - 2^{-c\,nm}.
--   $$
--   Here $x'$ ranges over $\{0,1\}^n$.
--
--   In the proof of Claim 4.7 this turns an inverter for the family $\mathcal H'$ into one that succeeds on uniform targets $y$, which is what the pre-image sampler needs.
--
--   Differences from the source:
--   - generalization: A is any efficient algorithm → A is any map from (description of f, target, coins) to a string; reason: the proof uses only the PRF security of f (the max-load test), never A's efficiency; efficient algorithms are a special case
--   - generalization: H is a sub-exponentially secure PRF (an efficient keyed family) → only oracle security of the keyed family is assumed, no efficiency; reason: the proof uses only oracle indistinguishability; every efficient sub-exponentially secure PRF satisfies the hypothesis
--   - reading: sub-exponentially secure PRF → oracle indistinguishability from a random function against non-uniform adaptive oracle distinguishers of size ≤ p(λ) for all n, m ≤ p(λ), advantage ≤ 2^{-λ^δ}; reason: standard definition with §3's sub-exponential security; the distinguisher encoding is polynomially equivalent to oracle circuits
--   - reading: "a sufficiently large λ = poly(n, m)" and 2^{-Ω(nm)} → ∃ c > 0, k₀, n₀ placed before A; λ ≥ (n + m)^{k₀}, n ≥ n₀; reason: the hidden constants come from the PRF's δ, not from A
--   - encoding: nm in the denominator → hypothesis m ≥ 1; reason: excludes only the undefined case m = 0
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 4.10, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_NearOptOWF_KeyedFam_IsSubexpPRF
import Definitions.Def_LaconicBarrier_RunsWithin

namespace NearOptOWF

open LaconicBarrier

/-- **Lemma 4.10** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 4.10, p.17 (PDF p.19)): let `K = {f : {0,1}ⁿ → {0,1}ᵐ}` be a
sub-exponentially secure PRF. There are `c > 0`, an exponent `k₀` and a threshold `n₀` such that for all
`n ≥ n₀`, `m ≥ 1` and `λ ≥ (n + m)^{k₀}`, every randomized algorithm `A` and every real `ε`: if
`Pr_{f←K, x←{0,1}ⁿ}[A(f, f(x)) = x′ ∧ f(x′) = f(x)] ≥ ε`, then
`Pr_{f←K, y←{0,1}ᵐ}[A(f, y) = x′ ∧ f(x′) = y] ≥ (2^{min{n,m}−m}/(nm)) · ε − 2^{−c·n·m}`.

**Formalization Note** "`2^{−Ω(nm)}`" and "a sufficiently large `λ = poly(n, m)`" are `∃ c, k₀, n₀`
placed before `A`. `A` is any map from (description of `f`, target, coins) to a string; the lemma's
"efficient" is not needed, since the proof uses only the PRF security of `f`. A success means
`x′ ∈ {0,1}ⁿ`. -/
theorem lemma_4_10 (K : KeyedFam) (hK : K.IsSubexpPRF) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ n₀ : ℕ, ∀ n m lam : ℕ, n₀ ≤ n → 1 ≤ m → (n + m) ^ k₀ ≤ lam →
      ∀ (a : ℕ) (A : List Bool → List Bool → (Fin a → Bool) → List Bool) (ε : ℝ),
        ε ≤ coinAvg (K.keyLen lam n m) (fun key => coinAvg n (fun x => coinAvg a (fun r =>
          if (A (K.circ lam n m key).code ((K.circ lam n m key).eval (bits x)) r).length = n ∧
              (K.circ lam n m key).eval
                (A (K.circ lam n m key).code ((K.circ lam n m key).eval (bits x)) r) =
                (K.circ lam n m key).eval (bits x)
          then 1 else 0))) →
        (2 : ℝ) ^ (((min n m : ℕ) : ℝ) - (m : ℝ)) / ((n : ℝ) * m) * ε - (2 : ℝ) ^ (-(c * n * m)) ≤
          coinAvg (K.keyLen lam n m) (fun key => coinAvg m (fun y => coinAvg a (fun r =>
            if (A (K.circ lam n m key).code (bits y) r).length = n ∧
                (K.circ lam n m key).eval (A (K.circ lam n m key).code (bits y) r) = bits y
            then 1 else 0))) := by sorry

end NearOptOWF
