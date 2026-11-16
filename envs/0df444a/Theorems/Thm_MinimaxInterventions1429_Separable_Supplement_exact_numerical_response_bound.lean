-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_exact_numerical_response_bound
-- name    : MinimaxInterventions1429.Separable.Supplement.exact_numerical_response_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:23:49.344202+00:00
-- url     : https://prove2.me/theorems/a9418ad6-64c3-4a2a-b5fa-ed7e450fe351
-- title:
--   Theorem A.2 — Exact numerical-response query bound
-- statement:
--   Let $m,k\ge2$, $0<\lambda_0\le2$, $0<\gamma\le1/2$, and $L\in[0,1]^{m\times k}$ with $\Lambda(L)\ge\lambda_0$. The literal Appendix A algorithm, against arbitrary adversarial exact numerical minimizers, returns $\widehat L$ with $d_q(\widehat L,L)\le\gamma$. Its surcharges are bounded separable and its call count is at most
--   $$Q=(mk-1)\left\lceil\log_2\frac{2^{16}}{\lambda_0}\right\rceil+2(m-1)(k-1)+(k-1)\left\lceil\log_2\frac1\gamma\right\rceil.$$
--   The asymptotic consequence is retained by the explicit uniform witness
--   $$Q\le20\left(mk\log_2(4/\lambda_0)+(k-1)\log_2(1/\gamma)\right).$$
--   This bound applies to all possible complete numerical transcripts, with correctness on realized exact transcripts, including adversarial choices at ties outside the unique two-probe stage.
--
--   Differences from the source:
--   - encoding: the three-term ceiling count and O(mk log(4/lambda_0)+(k-1)log(1/gamma)) → the exact natural-number budget and the explicit base-two-log multiplier 20; reason: ceil x <= x+1 and log_2(4/lambda_0) >= 1 give a uniform witness without replacing the finite bound
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem A.2, printed p.28 (PDF p.30)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Numerical
set_option autoImplicit false
universe u_exact_numerical_response_bound

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem exact_numerical_response_bound
    {m k : ℕ} [NeZero m] [NeZero k] (hm : 2 ≤ m) (hk : 2 ≤ k)
    (lam γ : ℝ) (hlam : 0 < lam ∧ lam ≤ 2) (hγ : 0 < γ ∧ γ ≤ 1/2) :
    (exactNumerical m k lam γ).usesAtMost (exactQueryBudget m k lam γ) ∧
    (exactNumerical m k lam γ).queriesSatisfy Allowed ∧
    ((exactQueryBudget m k lam γ : ℕ) : ℝ) ≤
      20*((m*k : ℕ)* (Real.log (4/lam)/Real.log 2) +
        (k-1 : ℕ)*(Real.log (1/γ)/Real.log 2)) ∧
    ∀ (L : Table m k) (O : NumericalOracle m k), InCube L → lam ≤ interaction L →
      numericalAccurate L 0 ((exactNumerical m k lam γ).run O []).2 →
      ∃ M, ((exactNumerical m k lam γ).run O []).1 = some M ∧ quotientDist M L ≤ γ := by sorry

end MinimaxInterventions1429.Separable.Supplement
