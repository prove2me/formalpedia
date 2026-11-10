-- Prove2me | Theorems.Thm_IntegerSumAmplification_Main_theorem_1_1
-- name    : IntegerSumAmplification.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:05:21.02787+00:00
-- url     : https://prove2.me/theorems/3fc90c65-8ffe-417c-97ce-a1a542c05a4e
-- title:
--   Theorem 1.1 — Range-free hardness amplification for integer sums
-- statement:
--   There exist absolute constants $c,C,Q>0$ with the following properties for every $n,m,s\in\mathbb N$, every $0<\delta,\varepsilon<1$, and every integer $k\ge32/(\delta\varepsilon^2)$. Let $U=\{0,1\}^n$, let $D$ be any probability law on $U$, and let $f:U\to\{0,\ldots,m-1\}$.
--
--   If every circuit of at most $s$ gates predicts $f$ under $D$ with probability at most $1-\delta$, then every circuit $A$ of the required sum-output width with
--   $$|A|\le \frac{c\varepsilon^2s}{\ln(1/\delta)}-C\ln(km)$$
--   satisfies
--   $$\Pr_{X_1,\ldots,X_k\sim D}[A(X_1,\ldots,X_k)=\textstyle\sum_i f(X_i)]\le\varepsilon.$$
--   All output bit strings are allowed in this circuit class; an out-of-range code is incorrect. The threshold is real, so a negative threshold admits no circuits.
--
--   In addition, every circuit predictor of the sum with success at least $\varepsilon$ (any output code of the sum width, not only codes in $\{0,\ldots,k(m-1)\}$) admits a deterministic oracle-circuit predictor $B^A$ for $f$, with output in the original range, error strictly below $\delta$, at most
--   $$Q\varepsilon^{-2}\ln(1/\delta)$$
--   oracle calls, and at most $Q\varepsilon^{-2}\ln(1/\delta)\ln(km)$ additional (non-oracle) Boolean gates. The circuit may contain nonuniform hardwired information fixed independently of the test input. The theorem retains the full domain $\delta\in(0,1)$ and the literal logarithm, including the source's recorded gap in deriving it from Theorem 5.1.
--
--   Differences from the source:
--   - encoding: binary words and one-based coordinates → Fin-indexed bits, little-endian decoding, and block concatenation; reason: these are bijective encodings; invalid output codes remain failures
--   - encoding: independent samples from D → the product probability measure D^k; reason: integration and event measures give exactly the stated expectations and probabilities
--   - encoding: bounded-fan-in Boolean circuits and oracle calls → well-formed LowDepthPRF circuits, actual gate counts and actual evaluation, without a depth restriction; reason: the published syntax has the source gate basis, free wiring and fan-out
--   - encoding: absolute O and Ω constants → positive real constants existentially quantified before every problem parameter; reason: this spells out uniform asymptotic bounds without introducing parameter-dependent constants
--   - encoding: size s′ = Ω(ε²s/log(1/δ)) minus O(log(km)) → actual natural gate counts bounded by a real threshold cε²s/ln(1/δ) minus C ln(km); reason: natural subtraction would change negative-threshold cases; natural logarithms only change absolute constants
--   - encoding: a reconstructed predictor for f → a deterministic nonuniform oracle circuit with range-valid output and error strictly below δ; reason: this uses the reconstruction-success contract in §3 and the nonuniform circuit setting of Theorem 5.1
--   - reading: our proof reconstructs a predictor for f using O(ε⁻² log(1/δ)) oracle calls → an oracle circuit with at most Qε⁻² ln(1/δ) oracle calls and at most Qε⁻² ln(1/δ) ln(km) additional Boolean gates; reason: the sentence refers (see Theorem 5.1) to the reconstruction whose Boolean overhead is O(log(km)) per call; without a bound on the non-oracle part a nonuniform circuit could compute f outright and the clause would be empty
--   - generalization: a predictor A for SUM_k ∘ f with values in {0, …, k(m−1)} → any well-formed circuit of the sum output width, out-of-range codes allowed; reason: more predictors are covered; on range-valued predictors it is exactly the source clause
-- source:
--   Farhan Ali and Weiqiang Yuan, Optimal Black-Box Hardness Amplification for Integer Sums, held manuscript dated November 3, 2026 (STOC 2027 submission; acceptance not asserted); citation_basis: published. Theorem 1.1, printed p. 2 / PDF p. 5; hardness and reconstruction-success contract in §3, printed p. 8 / PDF p. 11. PDF SHA256 181fd8ae5069b0c062ebccc0aa72d5a78ec0c836e6d8f6f99dd60464c0b746d7.

import Definitions.Def_IntegerSumAmplification_Main_CircuitPrediction
open MeasureTheory

namespace IntegerSumAmplification.Main

theorem theorem_1_1 : ∃ c C Q : ℝ, 0 < c ∧ 0 < C ∧ 0 < Q ∧
    ∀ (n m : ℕ) (δ ε : ℝ) (s k : ℕ), (0 < δ ∧ δ < 1) → (0 < ε ∧ ε < 1) →
    32 / (δ * ε ^ 2) ≤ (k : ℝ) →
    ∀ D : Measure (Bits n), IsProbabilityMeasure D → ∀ f : Bits n → Fin m,
    (HardAt m D (fun x => (f x).val) (s : ℝ) δ →
      ∀ A : LowDepthPRF.Circuit 0 0 (k * n) (wordWidth (sumRange k m)), A.WF →
        (A.size : ℝ) ≤ c * ε ^ 2 * s / Real.log (1 / δ) - C * Real.log ((k : ℝ) * m) →
        (productLaw D k).real {x | decode (A.evalPlain (pack x)) = ∑ i, (f (x i)).val} ≤ ε) ∧
    (∀ A : LowDepthPRF.Circuit 0 0 (k * n) (wordWidth (sumRange k m)), A.WF →
      ε ≤ (productLaw D k).real {x | decode (A.evalPlain (pack x)) = ∑ i, (f (x i)).val} →
      ∃ B : LowDepthPRF.Circuit (k * n) (wordWidth (sumRange k m)) n (wordWidth m),
        B.WF ∧ (B.queries : ℝ) ≤ Q / ε ^ 2 * Real.log (1 / δ) ∧
        (booleanGates B : ℝ) ≤ Q / ε ^ 2 * Real.log (1 / δ) * Real.log ((k : ℝ) * m) ∧
        (∀ x, decode (B.eval A.evalPlain x) < m) ∧
        D.real {x | decode (B.eval A.evalPlain x) ≠ (f x).val} < δ) := by sorry

end IntegerSumAmplification.Main
