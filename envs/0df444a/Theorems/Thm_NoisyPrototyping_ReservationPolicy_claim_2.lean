-- Prove2me | Theorems.Thm_NoisyPrototyping_ReservationPolicy_claim_2
-- name    : NoisyPrototyping.ReservationPolicy.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:55.750131+00:00
-- url     : https://prove2.me/theorems/47cca8ee-ba8e-479b-ad05-5b8ff9666407
-- title:
--   Claim 2, pp. A1–A2 (PDF 32–33) — Pandora's box problem P̂ with value laws g_i is equivalent to the noisy search problem
-- statement:
--   Under the hypotheses of Claim 1 (joint densities $f_i \ge 0$, $E|P_i| < \infty$, costs $w_i > 0$), let $g_i$ be the law of $X_i = Q_i(m_i)$, and let $\hat{\mathcal P}$ be Pandora's box problem in which box $i$ has value distribution $g_i$ and cost $w_i$. Then:
--
--   1. each $g_i$ is a probability distribution with finite mean;
--   2. for every order $\sigma$ and every prices $R$, if the reservation rule with prices $R$ and order $\sigma$ is admissible in $\hat{\mathcal P}$ then the fidelity-adjusted reservation rule $\pi^*$ is admissible in $\mathcal P_2$, and their expected net payoffs agree:
--   $$\mathbb E_{\mathcal P_2}[\text{net payoff of } \pi^*] = \mathbb E_{\hat{\mathcal P}}[\text{net payoff of the reservation rule}] ;$$
--   3. every policy admissible in $\mathcal P_2$ is matched by some policy admissible in $\hat{\mathcal P}$ with at least the same expected net payoff;
--   4. conversely, every policy admissible in $\hat{\mathcal P}$ is matched by some policy admissible in $\mathcal P_2$ with the same expected net payoff.
--
--   By 3 and 4 the two problems have the same optimal value. Together with Claim 1, the optimal value and an optimal policy of the noisy problem are those of $\hat{\mathcal P}$, which is the paper's "equivalent".
--
--   **Formalization Note** The proof's simplifying assumption that $Q_i$ is increasing with range $(-\infty,\infty)$ is not assumed (footnote 11 says it is only notational). Accordingly $g_i$ is the push-forward law of $Q_i(m_i)$, not the printed formula $\int f_i(P, Q^{-1}(x))\,dP$, which lacks the Jacobian. Formula (1) is read with $dP$ in the denominator.
-- source:
--   Bhaskaran and Erat, Optimal Prototyping with Noisy Measurements, author manuscript of 6 Nov 2024 (MSOM 2025, doi:10.1287/msom.2024.1133), pp. A1–A2 (PDF 32–33), Claim 2

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model

namespace NoisyPrototyping.ReservationPolicy
open MeasureTheory
theorem claim_2 {N : ℕ} (M : Model N) (f : Fin N → ℝ × ℝ → ℝ)
    (hf_nonneg : ∀ i z, 0 ≤ f i z) (hf_meas : ∀ i, Measurable (f i))
    (hlaw : ∀ i, M.law i =
      (volume : Measure (ℝ × ℝ)).withDensity (fun z => ENNReal.ofReal (f i z))) :
    (∀ i, IsProbabilityMeasure (g M.toSearchProblem (fun j => Q (f j)) i) ∧
      Integrable (fun x : ℝ => x) (g M.toSearchProblem (fun j => Q (f j)) i)) ∧
    (∀ (σ : Fin N ≃ Fin N) (R : Fin N → ℝ),
      (Admissible (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost)
          (fidelityPolicy (fun _ => id) σ R) →
        Admissible (M.toSearchProblem.posteriorProblem (fun j => Q (f j)))
          (fidelityPolicy (fun j => Q (f j)) σ R)) ∧
      value (M.toSearchProblem.posteriorProblem (fun j => Q (f j)))
          (fidelityPolicy (fun j => Q (f j)) σ R) =
        value (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost)
          (fidelityPolicy (fun _ => id) σ R)) ∧
    (∀ ρ : Policy N, Admissible (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ →
      ∃ ρ' : Policy N, Admissible (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost) ρ' ∧
        value (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ ≤
          value (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost) ρ') ∧
    ∀ ρ' : Policy N, Admissible (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost) ρ' →
      ∃ ρ : Policy N, Admissible (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ ∧
        value (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ =
          value (pandoraProblem (g M.toSearchProblem (fun j => Q (f j))) M.cost) ρ' := by sorry
end NoisyPrototyping.ReservationPolicy
