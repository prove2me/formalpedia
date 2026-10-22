-- Prove2me | Theorems.Thm_MultiStoreAssort_Approx_proposition7_half_approx
-- name    : MultiStoreAssort.Approx.proposition7_half_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:01.03899+00:00
-- url     : https://prove2.me/theorems/bdff2736-fdab-404d-8a09-3a6e1cd3bc06
-- title:
--   Proposition 7, PDF p. 24 — offering each store its single-store optimum earns at least ½ of the optimal SQR-heter revenue, and ½ is tight
-- statement:
--   Consider the heterogeneous multi-store model under sequential recommendation: $m$ stores with arrival fractions $\lambda_i\ge0$, $\sum_i\lambda_i=1$; $n$ products with revenues $r_1>r_2>\dots>r_n>0$; attraction values $v_{ik}>0$ of product $k$ in store $i$; utility discounts $c^k_{ij}\ge0$ with $c^k_{ii}=0$. Let $R(\boldsymbol S)$ be the (SQR-heter) revenue $\sum_i\lambda_i\sum_kr_kp^Q_{ik}(\boldsymbol S)$ of a profile $\boldsymbol S=(S_1,\dots,S_m)$, let $R^*_Q$ be its maximum over all profiles, and let $\tilde S_i$ be store $i$'s single-store optimal assortment (the smallest revenue-ordered maximizer of $\sum_{k\in S}r_kv_{ik}/(1+\sum_{k\in S}v_{ik})$). The heuristic offers $\tilde S_i$ in every store $i$ and earns $R^H_Q=R(\tilde S_1,\dots,\tilde S_m)$. Then:
--
--   1. **Half-approximation.**
--   $$
--   R^H_Q\ \ge\ \tfrac12R^*_Q.
--   $$
--   2. **Tightness.** For every $\delta>0$ there is an instance with two stores and two products, satisfying all of the above assumptions, on which $R^H_Q<(\tfrac12+\delta)R^*_Q$.
--
--   The result shows that the naive heuristic loses at most half of the optimal sequential revenue, and that sequential recommendation can earn up to twice the benchmark of operating every store separately.
--
--   **Formalization Note.** $R^*_Q$ is never formed as a term: part 1 states $\frac12R(\boldsymbol S)\le R^H_Q$ for every profile $\boldsymbol S$. The paper says it "identifies an instance where the equality holds", but its instance attains $\frac12$ only in the limit $\epsilon\to0$; part 2 states this limit form. Part 2 also asserts that $\tilde S_i$ exists on the instance, so it is not vacuous, and it uses the paper's tie rule: on the instance store 2 has two single-store optima, and only the smallest one makes the bound tight. The positivity of revenues is a pinned hypothesis (the paper's revenues are prices; its proof drops a second-stage revenue term that is nonnegative only for nonnegative prices). When $n=0$ no revenue-ordered assortment exists, so part 1 is vacuous there, as in the paper, where $\tilde S$ is a set $\{1,\dots,k\}$ with $k\in[n]$.
-- source:
--   Liu, Chen, Liu & Wan, Simultaneous vs. Sequential: Optimal Assortment Recommendation in Multistore Retailing, authors' manuscript with Online and Additional Supplements (2024-09-17; MSOM DOI 10.1287/msom.2024.0761), PDF p. 24, §7.1, Proposition 7; proof Online Supplement Appendix D.2, PDF pp. 46–47

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MultiStoreAssort_Approx_Model

namespace MultiStoreAssort.Approx

/-- Proposition 7 (p. 24): (1) offering each store `i` its single-store optimal assortment `S̃_i`
earns at least half the optimal (SQR-heter) revenue, `R^H_Q ≥ ½ R*_Q`; (2) the factor `½` is tight:
for every `δ > 0` there is an instance (two stores, two products) on which `R^H_Q < (½ + δ) R*_Q`. -/
theorem proposition7_half_approx :
    (∀ (m n : ℕ) (lam : Fin m → ℝ) (r : Fin n → ℝ) (v : Fin m → Fin n → ℝ)
        (c : Fin m → Fin m → Fin n → ℝ),
        (∀ i, 0 ≤ lam i) → ∑ i, lam i = 1 → StrictAnti r → (∀ k, 0 < r k) →
        (∀ i k, 0 < v i k) → (∀ i j k, 0 ≤ c i j k) → (∀ i k, c i i k = 0) →
        ∀ St : Fin m → Finset (Fin n), (∀ i, MultiStoreAssort.SMR.IsStilde r (v i) (St i)) →
          ∀ S : Fin m → Finset (Fin n), (1 / 2) * revQh lam r v c S ≤ revQh lam r v c St) ∧
    (∀ δ : ℝ, 0 < δ →
      ∃ (lam : Fin 2 → ℝ) (r : Fin 2 → ℝ) (v : Fin 2 → Fin 2 → ℝ) (c : Fin 2 → Fin 2 → Fin 2 → ℝ),
        (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ StrictAnti r ∧ (∀ k, 0 < r k) ∧
        (∀ i k, 0 < v i k) ∧ (∀ i j k, 0 ≤ c i j k) ∧ (∀ i k, c i i k = 0) ∧
        (∃ St : Fin 2 → Finset (Fin 2), ∀ i, MultiStoreAssort.SMR.IsStilde r (v i) (St i)) ∧
        ∀ St : Fin 2 → Finset (Fin 2), (∀ i, MultiStoreAssort.SMR.IsStilde r (v i) (St i)) →
          ∃ S : Fin 2 → Finset (Fin 2), revQh lam r v c St < (1 / 2 + δ) * revQh lam r v c S) := by sorry

end MultiStoreAssort.Approx
