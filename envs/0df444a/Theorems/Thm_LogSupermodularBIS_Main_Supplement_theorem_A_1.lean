-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_Supplement_theorem_A_1
-- name    : LogSupermodularBIS.Main.Supplement.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:35:06.634131+00:00
-- url     : https://prove2.me/theorems/676c6ef6-5961-4eb9-8b60-b29d5aae308e
-- title:
--   Theorem A.1 — bit-model counting, sampling and additive estimation
-- statement:
--   There are five uniform finite randomized bit programs and absolute constants $C>0$ and natural polynomial degrees $a,b$, all fixed before every input and accuracy parameter, with the following guarantees. All accuracy and failure parameters below are rational. Let $\ell_{\rm par}$ denote the total binary encoding length of the parameters for that invocation. Write
--   $$
--   E_G=n^{1/3}(\log n)^{4/3},\qquad E_W=\min\{d,d^{1/3}(\log d)^{2/3}(\log(d+B))^{2/3}\}.
--   $$
--   1. On any finite simple labeled bipartite graph $G$ with $n\ge2$ vertices and $0<\eta\le1/2$, the graph sampler always returns an independent set with law within total variation $\eta$ of the uniform law on independent sets, using
--   $$C e^{CE_G}(1+n+\log(1/\eta))^a(1+\ell_{\rm par})^b.$$
--   2. On the same graph and $\epsilon,\delta\in(0,1/2]$, the graph counter always returns a rational $\widehat Z$, with $\Pr[|\widehat Z/Z(G)-1|\le\epsilon]\ge1-\delta$, using
--   $$C e^{CE_G}(1+n+\epsilon^{-1}+\log(1/\delta))^a(1+\ell_{\rm par})^b.$$
--   3. Let $d\ge2$, $B\ge1$, and let $W:\{0,1\}^d\to\mathbb Q_{>0}$ be log-supermodular, with all value numerator and denominator lengths at most $B$ and exact evaluator bit cost bounded by $T_W$. For $0<\eta\le1/2$, the weight sampler always returns a configuration with law within total variation $\eta$ of $\mu_W=W/Z_W$, using
--   $$C e^{CE_W}(1+d+B+T_W+\log(1/\eta))^a(1+\ell_{\rm par})^b.$$
--   4. Under the same weight assumptions, for $\epsilon,\delta\in(0,1/2]$ the weight counter always returns a rational $\widehat Z$, with $\Pr[|\widehat Z/Z_W-1|\le\epsilon]\ge1-\delta$, using
--   $$C e^{CE_W}(1+d+B+T_W+\epsilon^{-1}+\log(1/\delta))^a(1+\ell_{\rm par})^b.$$
--   5. Under the same weight assumptions, for $0<\epsilon\le1/16$ and $0<\delta\le1/2$, the additive estimator always returns a rational $A$ satisfying
--   $$\Pr[\log Z_W-\epsilon d-1/8\le A\le\log Z_W]\ge1-\delta,$$
--   using
--   $$C\exp(C\epsilon^{-1/2}\log d\log(d+B))(1+d+B+T_W+\log(1/\delta))^a(1+\ell_{\rm par})^b.$$
--   Each bound counts bit operations and independent fair random bits on every execution, including accuracy failures. The weight programs access $W$ only through its exact evaluator. Neither $B$ nor $T_W$ must be polynomial in $d$. Graph programs have no evaluator. Rational outputs are actual binary numerator/denominator codes.
--
--   This companion theorem preserves the exponential factors of the exact-real results while providing finite-bit execution and unconditional output validity. It includes the full additive-estimation guarantee of Corollary 2.3 as its fifth clause.
--
--   Differences from the source:
--   - encoding: bit operations, independent fair bits, binary integer/rational storage and exact W evaluation → finite binary-stack programs with canonical self-delimiting binary input/output and charged exact evaluator queries; reason: an equivalent bit-cost model with only polynomial simulation overhead; query and answer lengths are charged, and no transcendental instruction is present
--   - encoding: same exponential factors and polynomial factors multiplied by poly(ℓpar) → C exp(C E)(1+sum of the displayed task parameters)^a(1+ℓpar)^b, with a single positive absolute C and natural degrees before all inputs; reason: unfolds O and poly uniformly; finite maxima permit common constants and degrees across the five algorithms
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 38 (PDF 39), Theorem A.1

import Mathlib
import Definitions.Def_LogSupermodularBIS_Main_Supplement_BitTasks

set_option autoImplicit false

namespace LogSupermodularBIS.Main.Supplement

/-- Theorem A.1, p.38 (PDF 39): all five bit-model guarantees, uniformly over the inputs.
The five finite programs and absolute constants/degrees precede every instance and parameter.
All costs count stack bit operations, fair random bits and exact evaluator bit cost. -/
theorem theorem_A_1 :
    ∃ SG CG SW CW A : BitProgram, ∃ C : ℝ, 0 < C ∧ ∃ a b : ℕ,
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), 2 ≤ n → G.IsBipartite →
        ∀ η : ℚ, HalfAccuracy η →
          BitSamples SG none (graphBitInput G [η]) n (uniformIndependent G)
            (IsIndependentConfig G) η
            (bitBound C a b (graphExponent n) [n, Real.log (1 / (η : ℝ))] [η])) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), 2 ≤ n → G.IsBipartite →
        ∀ ε δ : ℚ, HalfAccuracy ε → HalfAccuracy δ →
          BitCounts CG none (graphBitInput G [ε, δ]) (numIndependentSets G) ε δ
            (bitBound C a b (graphExponent n) [n, 1 / (ε : ℝ), Real.log (1 / (δ : ℝ))] [ε, δ])) ∧
      (∀ (d B TW : ℕ) (W : (Fin d → Bool) → ℚ), StandingWeight W B →
        LogSupermodular W → ∀ η : ℚ, HalfAccuracy η →
          BitSamples SW (weightBitOracle W TW) (weightBitInput d B [η]) d (gibbsLaw W)
            (fun _ => True) η
            (bitBound C a b (weightExponent d B) [d, B, TW, Real.log (1 / (η : ℝ))] [η])) ∧
      (∀ (d B TW : ℕ) (W : (Fin d → Bool) → ℚ), StandingWeight W B →
        LogSupermodular W → ∀ ε δ : ℚ, HalfAccuracy ε → HalfAccuracy δ →
          BitCounts CW (weightBitOracle W TW) (weightBitInput d B [ε, δ]) (partitionFn W) ε δ
            (bitBound C a b (weightExponent d B)
              [d, B, TW, 1 / (ε : ℝ), Real.log (1 / (δ : ℝ))] [ε, δ])) ∧
      (∀ (d B TW : ℕ) (W : (Fin d → Bool) → ℚ), StandingWeight W B →
        LogSupermodular W → ∀ ε δ : ℚ, 0 < ε → ε ≤ 1 / 16 → HalfAccuracy δ →
          BitAdditive A (weightBitOracle W TW) (weightBitInput d B [ε, δ]) d (partitionFn W) ε δ
            (bitBound C a b ((ε : ℝ) ^ (- (1 / 2 : ℝ)) * Real.log d * Real.log ((d : ℝ) + B))
              [d, B, TW, Real.log (1 / (δ : ℝ))] [ε, δ])) := by sorry

end LogSupermodularBIS.Main.Supplement
