-- Prove2me | Theorems.Thm_OptStochMatch_Tight_theorem_1_1
-- name    : OptStochMatch.Tight.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:56:33.193579+00:00
-- url     : https://prove2.me/theorems/1a3d528a-b637-411d-906e-b2a076fc977c
-- title:
--   Theorem 1.1 — the optimal competitive ratio is $1-e/e^e$ for Poisson and i.i.d. arrivals, attained in polynomial time
-- statement:
--   The optimal competitive ratios for Poisson and i.i.d. arrivals satisfy $\mathrm{CR}=\mathrm{CR}_{\mathrm{iid}}=1-e/e^e$. Moreover, this guarantee can be achieved in polynomial time: one randomized online algorithm, run at each arrival by a polynomial-time Turing machine on the explicit binary input, the unmatched set, the arriving type and polynomially many fair random bits, has expected matching size at least $(1-e/e^e)\,\mathrm{OPT}$ on every Poisson instance and at least $(1-e/e^e)\,\mathrm{OPT}_n$ on every i.i.d. instance.
--
--   Differences from the source:
--   - encoding: online policies: decisions from the current arrival, the history and independent internal randomization → PoissonPolicy / IIDPolicy: one Uniform[0,1] seed and a decision map measurable in the seed and arrival times; reason: a single uniform seed generates any independent internal randomness; past decisions are functions of the seed and past arrivals; same policy class
--   - encoding: CR and CRiid as inf over instances with OPT > 0 of sup over algorithms knowing the instance → real sInf over instances (m, λ) resp. (n ≥ 1, m, µ with ∑µ = 1) with OPT > 0 of real sSup of ALG/OPT over policies of that instance; reason: the inner sets are nonempty and bounded (ALG ≤ m), the outer set is nonempty and bounded below by 0, so sInf/sSup are the source's inf/sup
--   - encoding: Poisson processes of intensities λ_S on [0,1] → Janossy densities e^{−∑λ_S} ∏ λ_{s_k} on ordered arrival times; reason: the law of the superposition of independent type-wise Poisson processes; same law
--   - reading: 'polynomial time' with no machine model fixed → Mathlib's Turing.TM2ComputableInPolyTime per arrival on the explicit binary input (positive-rate types, binary rationals), the unmatched set and the arriving type as m-bit strings, and p(|input|+m) fair random bits; reason: the source fixes the explicit input and the measure of complexity (p. 26) but no machine model; a multi-stack Turing machine with a polynomial step bound is the standard worst-case model and is not vacuous
--   - generalization: a randomized online algorithm with worst-case polynomial preprocessing and time per arrival → the machine sees only the explicit input, the unmatched set, the arriving type and fresh random bits, recomputes everything at every arrival, and must work for every listing order of the input; reason: such a machine supplies the full printed polynomial-time guarantee. The exact balanced rule is memoryless; the printed truncation keeps a fallback flag (PDF p. 42). A memoryless version instead uses greedy only on the failing choice: the same first-failure coupling bounds loss by M m 2^(−k) for each arrival sequence of optimum M, regardless of subsequent choices. It therefore retains the ratio and works for every listing order
--   - reading: 'In both arrival models, there is a randomized online matching algorithm' → one machine f and one random-bit polynomial p serve both models; reason: the quantifier is ambiguous; the stronger reading is taken, as in Theorem 1.1 (one guarantee in polynomial time) and §6 (the same algorithm, with λ = nµ)
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Theorem 1.1, p. 1 (PDF p. 2)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Matching
import Definitions.Def_OptStochMatch_Tight_Machine
open scoped NNReal BigOperators

namespace OptStochMatch.Tight

/-- Theorem 1.1 (p. 1, PDF 2). The optimal competitive ratios for Poisson and i.i.d. arrivals
satisfy `CR = CRiid = 1 − e/e^e`. Moreover, this guarantee can be achieved in polynomial time:
one randomized online algorithm, run per arrival by a polynomial-time Turing machine on the
explicit binary input, the unmatched set, the arriving type and polynomially many fair random
bits, attains ratio `1 − e/e^e` on every instance of both models. -/
theorem theorem_1_1 :
    CR = cStar ∧ CRiid = cStar ∧
    ∃ (f : List Bool → List Bool) (p : Polynomial ℕ), PolyTimeBits f ∧
      (∀ (m : ℕ) (lam : Ty m → ℝ≥0) (L : List (Ty m × ℚ)), IsListing lam L →
        cStar * optPoisModel lam ≤ algRoutePois lam (machineRule f p L)) ∧
      (∀ (m n : ℕ) (mu : Ty m → ℝ≥0) (L : List (Ty m × ℚ)), 1 ≤ n → ∑ S, mu S = 1 →
        IsListing (iidRates n mu) L →
        cStar * optIID n mu ≤ algRouteIID n mu (machineRule f p L)) := by sorry

end OptStochMatch.Tight
