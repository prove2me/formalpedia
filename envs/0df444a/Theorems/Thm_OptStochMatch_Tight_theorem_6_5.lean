-- Prove2me | Theorems.Thm_OptStochMatch_Tight_theorem_6_5
-- name    : OptStochMatch.Tight.theorem_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:56:38.419501+00:00
-- url     : https://prove2.me/theorems/a5a40932-f9e3-400f-aad3-67afded4aeaa
-- title:
--   Theorem 6.5 — one polynomial-time randomized online algorithm with ratio 1 − e^{1−e} in both models
-- statement:
--   There is one randomized online matching algorithm, run at each arrival by a polynomial-time Turing machine on the explicit binary input (types with positive rate, rational rates in binary; $\lambda=n\mu$ in the i.i.d. model), the unmatched set, the arriving type and polynomially many fair random bits, with expected matching size at least $(1-e^{1-e})\,\mathrm{OPT}$ on every Poisson instance and at least $(1-e^{1-e})\,\mathrm{OPT}_n$ on every i.i.d. instance.
--
--   Differences from the source:
--   - reading: 'polynomial time' with no machine model fixed → Mathlib's Turing.TM2ComputableInPolyTime per arrival on the explicit binary input (positive-rate types, binary rationals), the unmatched set and the arriving type as m-bit strings, and p(|input|+m) fair random bits; reason: the source fixes the explicit input and the measure of complexity (p. 26) but no machine model; a multi-stack Turing machine with a polynomial step bound is the standard worst-case model and is not vacuous
--   - generalization: a randomized online algorithm with worst-case polynomial preprocessing and time per arrival → the machine sees only the explicit input, the unmatched set, the arriving type and fresh random bits, recomputes everything at every arrival, and must work for every listing order of the input; reason: such a machine supplies the full printed polynomial-time guarantee. The exact balanced rule is memoryless; the printed truncation keeps a fallback flag (PDF p. 42). A memoryless version instead uses greedy only on the failing choice: the same first-failure coupling bounds loss by M m 2^(−k) for each arrival sequence of optimum M, regardless of subsequent choices. It therefore retains the ratio and works for every listing order
--   - reading: 'In both arrival models, there is a randomized online matching algorithm' → one machine f and one random-bit polynomial p serve both models; reason: the quantifier is ambiguous; the stronger reading is taken, as in Theorem 1.1 (one guarantee in polynomial time) and §6 (the same algorithm, with λ = nµ)
--   - encoding: Poisson processes of intensities λ_S on [0,1] → Janossy densities e^{−∑λ_S} ∏ λ_{s_k} on ordered arrival times; reason: the law of the superposition of independent type-wise Poisson processes; same law
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Theorem 6.5, p. 30 (PDF p. 31), with the computational model of §6, p. 26 (PDF p. 27)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Matching
import Definitions.Def_OptStochMatch_Tight_Machine
open scoped NNReal BigOperators

namespace OptStochMatch.Tight

/-- Theorem 6.5 (p. 30, PDF 31). There is one randomized online matching algorithm, run per
arrival by a polynomial-time Turing machine on the explicit binary input (positive-rate types
with rational rates; `λ = nµ` in the i.i.d. model), the current unmatched set, the arriving type
and polynomially many fair random bits, whose expected matching size is at least
`(1 − e^{1−e}) OPT` on every Poisson instance and at least `(1 − e^{1−e}) OPT_n` on every i.i.d.
instance. -/
theorem theorem_6_5 :
    ∃ (f : List Bool → List Bool) (p : Polynomial ℕ), PolyTimeBits f ∧
      (∀ (m : ℕ) (lam : Ty m → ℝ≥0) (L : List (Ty m × ℚ)), IsListing lam L →
        cStar * optPoisModel lam ≤ algRoutePois lam (machineRule f p L)) ∧
      (∀ (m n : ℕ) (mu : Ty m → ℝ≥0) (L : List (Ty m × ℚ)), 1 ≤ n → ∑ S, mu S = 1 →
        IsListing (iidRates n mu) L →
        cStar * optIID n mu ≤ algRouteIID n mu (machineRule f p L)) := by sorry

end OptStochMatch.Tight
