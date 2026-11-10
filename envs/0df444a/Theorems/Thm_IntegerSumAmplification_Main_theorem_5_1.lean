-- Prove2me | Theorems.Thm_IntegerSumAmplification_Main_theorem_5_1
-- name    : IntegerSumAmplification.Main.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:05:10.544622+00:00
-- url     : https://prove2.me/theorems/2cb7dccc-8213-4d94-81b8-cf0cdb94ba2d
-- title:
--   Theorem 5.1 — Non-uniform reconstruction
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $U=\{0,1\}^n$, $m\ge2$, $0<\delta,\varepsilon<1$, and $k\ge32/(\delta\varepsilon^2)$. Let $D$ be any joint law on $U\times\{0,\ldots,m-1\}$, and let $A:U^k\to\{0,\ldots,k(m-1)\}$ be a Boolean circuit with
--   $$\Pr[A(X_1,\ldots,X_k)=\textstyle\sum_iY_i]\ge\varepsilon$$
--   for independent $(X_i,Y_i)\sim D$. Put
--   $$L=\left\lceil\frac8{\varepsilon^2}\ln\frac8\delta\right\rceil.$$
--   There exists a deterministic oracle circuit $B^A:U\to\{0,\ldots,m-1\}$ making at most $L$ calls to $A$, using at most $CL\ln(km)$ additional Boolean gates, and satisfying
--   $$\Pr_{(X,Y)\sim D}[B^A(X)=Y]\ge1-\delta/2.$$
--   Moreover, if $s'=|A|$ is the gate count of $A$, there is a plain Boolean circuit with exactly the same output as $B^A$ on every input and at most $CL(s'+\ln(km))$ gates. The law $D$ may have nondeterministic labels; all constants are independent of it and of all parameters and circuits.
--
--   Differences from the source:
--   - encoding: binary words and one-based coordinates → Fin-indexed bits, little-endian decoding, and block concatenation; reason: these are bijective encodings; invalid output codes remain failures
--   - encoding: independent samples from D → the product probability measure D^k; reason: integration and event measures give exactly the stated expectations and probabilities
--   - encoding: bounded-fan-in Boolean circuits and oracle calls → well-formed LowDepthPRF circuits, actual gate counts and actual evaluation, without a depth restriction; reason: the published syntax has the source gate basis, free wiring and fan-out
--   - encoding: absolute O and Ω constants → positive real constants existentially quantified before every problem parameter; reason: this spells out uniform asymptotic bounds without introducing parameter-dependent constants
--   - encoding: O bounds using log(km) and an implementation after substitution → natural logarithms and existence of an actual equivalent plain circuit with its actual gate count; reason: changing the logarithm base changes only the absolute constant; equivalence is checked on every input
-- source:
--   Farhan Ali and Weiqiang Yuan, Optimal Black-Box Hardness Amplification for Integer Sums, held manuscript dated November 3, 2026 (STOC 2027 submission; acceptance not asserted); citation_basis: published. Theorem 5.1, printed p. 11 / PDF p. 14; implementation proof printed pp. 18–19 / PDF pp. 21–22. PDF SHA256 181fd8ae5069b0c062ebccc0aa72d5a78ec0c836e6d8f6f99dd60464c0b746d7.

import Definitions.Def_IntegerSumAmplification_Main_CircuitPrediction
open MeasureTheory

namespace IntegerSumAmplification.Main

theorem theorem_5_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (n m k : ℕ) (δ ε : ℝ), 2 ≤ m → (0 < δ ∧ δ < 1) → (0 < ε ∧ ε < 1) →
    32 / (δ * ε ^ 2) ≤ (k : ℝ) →
    ∀ D : Measure (LabeledInput n m), IsProbabilityMeasure D →
    ∀ A : LowDepthPRF.Circuit 0 0 (k * n) (wordWidth (sumRange k m)),
    A.WF → (∀ x, decode (A.evalPlain x) < sumRange k m) →
    ε ≤ (productLaw D k).real {z |
      decode (A.evalPlain (pack (fun i => (z i).1))) = ∑ i, (z i).2.val} →
    ∃ B : LowDepthPRF.Circuit (k * n) (wordWidth (sumRange k m)) n (wordWidth m),
      B.WF ∧ B.queries ≤ reconstructionBudget δ ε ∧
      (booleanGates B : ℝ) ≤ C * reconstructionBudget δ ε * Real.log ((k : ℝ) * m) ∧
      (∀ x, decode (B.eval A.evalPlain x) < m) ∧
      1 - δ / 2 ≤ D.real {z | decode (B.eval A.evalPlain z.1) = z.2.val} ∧
      (∃ T : LowDepthPRF.Circuit 0 0 n (wordWidth m), T.WF ∧
        (T.size : ℝ) ≤ C * reconstructionBudget δ ε * ((A.size : ℝ) + Real.log ((k : ℝ) * m)) ∧
        ∀ x, T.evalPlain x = B.eval A.evalPlain x) := by sorry

end IntegerSumAmplification.Main
