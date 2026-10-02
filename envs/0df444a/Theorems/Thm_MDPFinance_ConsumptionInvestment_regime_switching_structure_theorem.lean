-- Prove2me | Theorems.Thm_MDPFinance_ConsumptionInvestment_regime_switching_structure_theorem
-- name    : MDPFinance.ConsumptionInvestment.regime_switching_structure_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:56.924844+00:00
-- url     : https://prove2.me/theorems/38ab5ab4-255b-439c-a4e6-4ef531b79ca3
-- title:
--   Theorem 4.4.1 — the regime-switching structure theorem
-- statement:
--   a) $x \mapsto J_n(x,j)$ is strictly increasing, strictly concave, continuous for every $j$;
--   b) $J_0(x,j)=U_p(x)$, $J_{n+1}(x,j) = \sup_{(c,a)}[U_c(c) + \beta\sum_k p_{jk}\int
--   J_n((1+i)(x-c+a\cdot z),k)\,Q_j(dz)]$; c) maximizers exist and assemble into an optimal $N$-stage
--   policy.
--
--   **Formalization Note.** Generalizes chunk `04a`'s Theorem 4.2.2/this chunk's Theorem 4.3.3
--   pattern to a regime-augmented state; the policy sequence's reindexing $\pi(l) := f^*_{N-l}$
--   mirrors chunk `02d`'s `structure_theorem_stationary` for the same reason (a stationary model's
--   Forward-Induction output, translated into a time-indexed policy).
--
--   **Formalization Note (moderation).** Values are $[-\infty,\infty)$-valued and the standing
--   assumptions of Section 4.4 are carried by the model.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 102, PDF 116, Theorem 4.4.1

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimeMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- Theorem 4.4.1 (Bäuerle–Rieder, p. 102, PDF 116). a) `x ↦ J_n(x,j)` is strictly increasing,
strictly concave and continuous for every `j`; b) `J_0(x,j) = U_p(x)`,
`J_{n+1}(x,j) = sup_{(c,a) ∈ D(x,j)} [U_c(c) + β Σ_{k} p_{jk} ∫ J_n((1+i)(x-c+a·z),k) Q_j(dz)]`;
c) maximizers `f_n^*` of `J_{n-1}` exist and `(f_N^*,…,f_1^*)` is optimal for the `N`-stage
consumption-investment problem with regime switching: the policy sequence `π(l) := f^*_{N-l}`
for `l = 0,…,N-1` attains `J_N`. -/
theorem regime_switching_structure_theorem {EY : Type*} [Fintype EY] [MeasurableSpace EY]
    {d : ℕ} (M : RegimeSwitchingMarket EY d) (N : ℕ) :
    (∀ n ≤ N, ∀ j : EY, StrictMonoOn (fun x => M.J n x j) M.domU ∧
        StrictConcaveOnEReal M.domU (fun x => M.J n x j) ∧
        ContinuousOn (fun x => M.J n x j) M.domU) ∧
      (∀ x ∈ M.domU, ∀ j, M.J 0 x j = (M.Up x : EReal)) ∧
      (∀ n, ∀ x ∈ M.domU, ∀ j : EY,
        M.J (n + 1) x j = ⨆ ca ∈ M.D x j,
          (M.Uc ca.1 : EReal) + (M.β : EReal) * ∑ k, (M.p j k : EReal) *
            erealIntegral (M.Q j) (fun z => M.J n ((1 + M.i) * (x - ca.1 + ∑ m, ca.2 m * z m)) k)) ∧
      (∃ fstar : ℕ → ℝ × EY → ℝ × (Fin d → ℝ),
        (∀ n, 1 ≤ n → n ≤ N → (∀ x ∈ M.domU, ∀ j, fstar n (x, j) ∈ M.D x j) ∧
          Measurable (fstar n) ∧
          ∀ x ∈ M.domU, ∀ j : EY,
            (M.Uc (fstar n (x, j)).1 : EReal) + (M.β : EReal) * ∑ k, (M.p j k : EReal) *
              erealIntegral (M.Q j) (fun z => M.J (n - 1) ((1 + M.i) * (x - (fstar n (x, j)).1 +
                ∑ m, (fstar n (x, j)).2 m * z m)) k) = M.J n x j) ∧
        M.IsAdmissible N (fun l => fstar (N - l)) ∧
        ∀ x ∈ M.domU, ∀ j : EY, M.Jpi (fun l => fstar (N - l)) N x j = M.J N x j) := by sorry

end MDPFinance.ConsumptionInvestment
