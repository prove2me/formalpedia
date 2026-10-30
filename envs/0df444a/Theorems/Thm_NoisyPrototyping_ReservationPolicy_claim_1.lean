-- Prove2me | Theorems.Thm_NoisyPrototyping_ReservationPolicy_claim_1
-- name    : NoisyPrototyping.ReservationPolicy.claim_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:52.788105+00:00
-- url     : https://prove2.me/theorems/1c09ff29-70e2-4f86-a515-b765cdd63dcc
-- title:
--   Claim 1, p. A1 (PDF 32) — the problem P₂ that pays the posterior mean Q_i(m_i) is equivalent to the original noisy search problem P
-- statement:
--   Let $\mathcal P$ be the noisy search model with $N$ prototypes, where $(P_i, m_i)$ has a measurable joint density $f_i \ge 0$, $E|P_i| < \infty$, and evaluation costs $w_i > 0$. Let $Q_i$ be formula (1) for $f_i$, and let $\mathcal P_2$ be the search problem with the same measurements and costs in which stopping and selecting prototype $i$ yields $Q_i(m_i)$ instead of $P_i$.
--
--   Then for every adaptive policy $\rho$ (which sees only measurements):
--
--   1. $\rho$ is admissible in $\mathcal P$ if and only if it is admissible in $\mathcal P_2$;
--   2. if it is admissible, its expected net payoff is the same in both problems:
--   $$\mathbb E_{\mathcal P}[\text{net payoff of } \rho] = \mathbb E_{\mathcal P_2}[\text{net payoff of } \rho].$$
--
--   In particular the two problems have the same optimal policies and the same optimal value, which is the paper's "equivalent".
--
--   **Formalization Note** $\mathcal P_2$ is `posteriorProblem`, whose law for prototype $i$ is the law of $(Q_i(m_i), m_i)$. The measurement $m_i$ in $\mathcal P_2$ has its original distribution, the marginal $\int f_i(P, m)\,dP$ of the page. Formula (1) is read with $dP$ in the denominator.
-- source:
--   Bhaskaran and Erat, Optimal Prototyping with Noisy Measurements, author manuscript of 6 Nov 2024 (MSOM 2025, doi:10.1287/msom.2024.1133), p. A1 (PDF 32), Claim 1 and (A.1)

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model

namespace NoisyPrototyping.ReservationPolicy
open MeasureTheory
theorem claim_1 {N : ℕ} (M : Model N) (f : Fin N → ℝ × ℝ → ℝ)
    (hf_nonneg : ∀ i z, 0 ≤ f i z) (hf_meas : ∀ i, Measurable (f i))
    (hlaw : ∀ i, M.law i =
      (volume : Measure (ℝ × ℝ)).withDensity (fun z => ENNReal.ofReal (f i z)))
    (ρ : Policy N) :
    (Admissible M.toSearchProblem ρ ↔
      Admissible (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ) ∧
    (Admissible M.toSearchProblem ρ →
      value M.toSearchProblem ρ =
        value (M.toSearchProblem.posteriorProblem (fun j => Q (f j))) ρ) := by sorry
end NoisyPrototyping.ReservationPolicy
