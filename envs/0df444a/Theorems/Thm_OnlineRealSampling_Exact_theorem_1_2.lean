-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_theorem_1_2
-- name    : OnlineRealSampling.Exact.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:16:39.567172+00:00
-- url     : https://prove2.me/theorems/2a7d963a-1cb7-4f6c-8cd4-4d2c755f5ae9
-- title:
--   Theorem 1.2 — exact online sampling with $O(\log n)$ entropy loss and $O(\log i)$ persistent space
-- statement:
--   Run Algorithm 2 with $\epsilon=0$. The CDF oracles $F_1,F_2,\dots$ arrive online and are chosen by an environment from the public history $X_1,\dots,X_{i-1}$ and external randomness $\xi$ that is independent of the fair bits. Then:
--
--   1. **Exactness.** For every $\xi$, almost surely every iteration halts, and for every $n$ and $x_1,\dots,x_n$
--   $$\Pr(X_1=x_1,\dots,X_n=x_n\mid\xi)=\prod_{i=1}^n f_i(x_i),$$
--   where $f_i$ is the PMF of the oracle chosen after the history $x_1,\dots,x_{i-1}$. Thus $X_i\sim F_i$ conditionally on the history.
--   2. **Entropy loss.** For an admissible environment and every $n\ge1$, the entropy loss is well defined and
--   $$0\le L_n\le 11\lg(n+2)=O(\log n).$$
--   3. **Resources at iteration $i\ge1$.** There is an absolute constant $K$, valid for every word size, every admissible environment and every $i$, with:
--      - 1.2.1: the persistent space after iteration $i$ is at most $K\log i$ bits, deterministically;
--      - 1.2.2: the expected temporary space is at most $K(\log i+\mathbb E[\log X_i])$ bits;
--      - 1.2.3: the expected number of oracle calls is at most $K\,\mathbb E[\log X_i]$;
--      - 1.2.4: the expected number of big-integer arithmetic operations is at most $K\,\mathbb E[\log X_i]$, and the expected maximum bit length of their operands is at most $K(\log i+\mathbb E[\log X_i])$.
--   4. **1.2.5, running time.** For every polynomial $g$ there is $K_g$ such that, if each oracle offered at iteration $i$ has a cost function $C_{F_i}$ that is efficient with polynomial $g$ in the sense of (7) and (8) and chosen measurably, the expected running time of iteration $i$ is at most
--   $$K_g\,\mathbb E\big[C_{F_i}(X_i,i)+\log(X_i)\,C_{F_i}(X_i,X_i)\big].$$
--   $C_{F_i}(x,\nu)$ bounds every oracle call at indices up to $x$ with precision up to $\lceil\lg\nu\rceil+1$, so this is the cost of $\log X_i$ invocations at $X_i$ with $\lg X_i$ bits of precision plus one invocation at $X_i$ with $\lg i$ bits.
--
--   The environment may make the targets depend on the earlier outputs. The supports may be countably infinite and the masses irrational; no finiteness of entropy or of the mean is assumed.
--
--   Differences from the source:
--   - generalization: there is an online algorithm with L_n ≤ O(log n) → Algorithm 2 with ε = 0, the source's own witness, with the explicit bound L_n ≤ 11 lg(n+2); reason: the concrete algorithm and constant (from Theorem 4.2) imply the existential O(log n) statement
--   - encoding: outputs X_i ∼ F_i, exact even conditioned on previous outputs → for every value ξ of the external randomness, the joint law of (X_1,…,X_n) under the fair bits is ∏ f_i(x_i), with almost-sure termination; reason: the product of the conditional laws is the joint law; conditioning on ξ is the source's conditioning on the history including external randomness
--   - encoding: L_n = E[T_n − Σ lg(1/f_i(X_i))] → integrability of the centred variable T_n − Σ lg(1/f_i(X_i)) is asserted, and L_n is its integral; reason: the source's expectation exists; asserting integrability rules out the default value 0 of a non-integrable integral
--   - encoding: L_n ≥ 0 in (3) → 0 ≤ L_n asserted as part of the conclusion; reason: (3) states the nonnegativity together with the definition
--   - reading: target F_i chosen from previous outputs and external randomness, independently of the sampler's state given X_1,…,X_{i-1} → F_i = env(ξ, [X_1,…,X_{i-1}]) with ξ ∼ μ independent of the fair bits, env measurable in ξ; reason: the source's information restriction, with external randomness drawn once as a seed; measurability is the convention needed for the expectations to be defined
--   - reading: for efficient oracles, running time within a constant factor of the expected cost of log X_i invocations at X_i with lg X_i bits of precision plus one invocation with lg i bits → E[time_i] ≤ K_g · E[C_{F_i}(X_i, i) + log(X_i) · C_{F_i}(X_i, X_i)], the constant depending only on the efficiency polynomial g; reason: the cost-function form established at the end of the proof (PDF 17): C_F(x,ν) bounds calls with precision ⌈lg ν⌉+1
--   - generalization: O(·) bounds for a fixed word size w ≥ 1 → one constant K valid for every word size w ≥ 1; reason: the source's constants do not depend on w; the statement specializes to each fixed w
--   - reading: Word RAM in which big-integer multiplication and division cost O(k log k) or Θ(k²) → concrete charged primitives: addition, subtraction and comparison cost limbs(a)+limbs(b); multiplication and division cost limbs(a)·limbs(b)+limbs(a)+limbs(b); shifts and powers of two cost the limbs of the result plus 1; bit length costs 1; every machine step costs at least 1; reason: the source leaves the multiplication algorithm open and names schoolbook as one option; C_F is assumed to dominate basic arithmetic under either choice
--   - encoding: expected values of resources that may be unbounded → lower Lebesgue integrals in [0, ∞], with the resource equal to ∞ on non-termination; reason: no junk value; the same instances, since termination is almost sure
--   - encoding: each IntervalSample iteration evaluates F⁺(X_mid, t) and, if needed, F⁻(X_mid, t) → one oracle call φ(X_mid, t+1) per iteration, from which both bounds are formed; reason: both bounds are φ(X_mid, t+1) ± 2^{-(t+1)} by (5); the deterministic oracle returns the same value, so this implements the pseudocode with at most the source's number of calls
--   - encoding: for efficient CDF oracles F_i → a cost-function family C(ξ, h) measurable in ξ, satisfying the cost-function conditions of §3 and efficiency (7)–(8) with polynomial g for every ξ and every history h of length i − 1; reason: measurability makes E[C_{F_i}(X_i, ·)] defined; histories of probability zero do not affect the law of the run, so their oracles can be replaced by efficient ones without changing either side
--   - encoding: L_n ≤ O(log n) → 0 ≤ L_n ≤ 11 lg(n+2) for every n ≥ 1; reason: L_n is defined in (3) for n ≥ 1
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Theorem 1.2, PDF 4 / printed 3; proof at the end of §6, PDF 16–17 / printed 15–16; constant 11 from Theorem 4.2, PDF 9 / printed 8

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Online

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Theorem 1.2. Algorithm 2 with `ε = 0`, fed CDF oracles `F₁, F₂, …` chosen adaptively from the
public history and independent external randomness, outputs `X₁ ∼ F₁, X₂ ∼ F₂, …` exactly
(conditionally on the history), with entropy loss `0 ≤ L_n ≤ 11 lg(n + 2) = O(log n)`, and at
iteration `i`:
1. persistent space `O(log i)` bits (deterministically);
2. expected temporary space `O(log i + E[log X_i])` bits;
3. expected number of oracle calls `O(E[log X_i])`;
4. expected number of big-integer arithmetic operations `O(E[log X_i])` and expected maximum
   operand bit length `O(log i + E[log X_i])`;
5. for efficient oracles (constant depending only on the polynomial `g` of (7)–(8)), expected
   running time `O(E[C_{F_i}(X_i, i) + log(X_i) C_{F_i}(X_i, X_i)])`. -/
theorem theorem_1_2 :
    (∀ (w : ℕ) (Ξ : Type) (env : Ξ → List ℕ → CDFOracle), (∀ ξ h, (env ξ h).Valid) →
      ∀ (ξ : Ξ) (n : ℕ),
        coinMeasure {ω | outputs w 0 env ξ ω n = none} = 0 ∧
        ∀ xs : List ℕ, xs.length = n →
          coinMeasure {ω | outputs w 0 env ξ ω n = some xs} =
            ∏ i ∈ Finset.range n, ENNReal.ofReal (pmf (env ξ (xs.take i)).F (xs.getD i 0))) ∧
    (∀ (w : ℕ) (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (env : Ξ → List ℕ → CDFOracle), AdmissibleEnv env → ∀ n : ℕ, 1 ≤ n →
      Integrable (lossVar w 0 env n) (onlineMeasure μ) ∧
        0 ≤ entropyLoss w μ 0 env n ∧ entropyLoss w μ 0 env n ≤ 11 * lg (n + 2)) ∧
    (∃ K : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ)
        [IsProbabilityMeasure μ] (env : Ξ → List ℕ → CDFOracle), AdmissibleEnv env →
      ∀ i : ℕ, 1 ≤ i →
        (∀ (p : Ξ × (ℕ → Bool)) (r : IterRecord), record w 0 env i p = some r →
          (r.after.bits : ℝ) ≤ K * slog i) ∧
        ∫⁻ p, iterResource w 0 env (fun r => r.usage.space) i p ∂(onlineMeasure μ) ≤
          ENNReal.ofReal K * (ENNReal.ofReal (slog i) +
            ∫⁻ p, logOutput w 0 env i p ∂(onlineMeasure μ)) ∧
        ∫⁻ p, iterResource w 0 env (fun r => r.usage.calls) i p ∂(onlineMeasure μ) ≤
          ENNReal.ofReal K * ∫⁻ p, logOutput w 0 env i p ∂(onlineMeasure μ) ∧
        ∫⁻ p, iterResource w 0 env (fun r => r.usage.ops) i p ∂(onlineMeasure μ) ≤
          ENNReal.ofReal K * ∫⁻ p, logOutput w 0 env i p ∂(onlineMeasure μ) ∧
        ∫⁻ p, iterResource w 0 env (fun r => r.usage.maxBits) i p ∂(onlineMeasure μ) ≤
          ENNReal.ofReal K * (ENNReal.ofReal (slog i) +
            ∫⁻ p, logOutput w 0 env i p ∂(onlineMeasure μ))) ∧
    (∀ g : Polynomial ℝ, ∃ K : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ (Ξ : Type) [MeasurableSpace Ξ]
        (μ : Measure Ξ) [IsProbabilityMeasure μ] (env : Ξ → List ℕ → CDFOracle)
        (Cb : Ξ → List ℕ → ℝ → ℝ → ℝ), AdmissibleEnv env →
        (∀ h x ν, Measurable (fun ξ => Cb ξ h x ν)) → ∀ i : ℕ, 1 ≤ i →
        (∀ ξ h, h.length = i - 1 →
          CostBound w (env ξ h).toOracleAccess (Cb ξ h) ∧ Efficient g (Cb ξ h)) →
        ∫⁻ p, iterResource w 0 env (fun r => r.usage.time) i p ∂(onlineMeasure μ) ≤
          ENNReal.ofReal K * ∫⁻ p, iterCostTerm w 0 env Cb i p ∂(onlineMeasure μ)) := by sorry

end OnlineRealSampling.Exact
