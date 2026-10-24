-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Regret_eq17_dr_error_decomposition
-- name    : OfflinePolicyLearning.Regret.eq17_dr_error_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:51.165054+00:00
-- url     : https://prove2.me/theorems/eff4c949-a46f-4542-b16e-9d82ab6d9b13
-- title:
--   (17), p. 22 — Δ̂(πa,πb) − Δ̃(πa,πb) = Σ_j (Δ̂^j_DR − Δ̃^j), each the sum of three error terms
-- statement:
--   For any sample $(X_i,A_i,Y_i)_{i=1}^n$, any cross-fitted estimators $\hat\mu^{-k}$, $\hat e^{-k}$ and any two policies $\pi^a,\pi^b$, write $\pi_j(X_i)=\mathbf 1\{\pi(X_i)=j\}$ for the $j$-th coordinate of the basis vector $\pi(X_i)$. Then
--   $$\hat\Delta(\pi^a,\pi^b)-\tilde\Delta(\pi^a,\pi^b)=\sum_{j=1}^d\big(S^j_1+S^j_2+S^j_3\big),$$
--   where
--   $$S^j_1=\frac1n\sum_{i=1}^n\big(\pi^a_j(X_i)-\pi^b_j(X_i)\big)\big(\hat\mu^{-k(i)}_j(X_i)-\mu_j(X_i)\big)\Big(1-\frac{\mathbf 1\{A_i=j\}}{e_j(X_i)}\Big),$$
--   $$S^j_2=\frac1n\sum_{i:\,A_i=j}\big(\pi^a_j(X_i)-\pi^b_j(X_i)\big)\big(Y_i-\mu_j(X_i)\big)\Big(\frac1{\hat e^{-k(i)}_j(X_i)}-\frac1{e_j(X_i)}\Big),$$
--   $$S^j_3=\frac1n\sum_{i:\,A_i=j}\big(\pi^a_j(X_i)-\pi^b_j(X_i)\big)\big(\mu_j(X_i)-\hat\mu^{-k(i)}_j(X_i)\big)\Big(\frac1{\hat e^{-k(i)}_j(X_i)}-\frac1{e_j(X_i)}\Big).$$
--
--   The decomposition splits the estimation error of the cross-fitted value differences into an (estimation error) × (noise) term, a (noise) × (estimation error) term and an (estimation error) × (estimation error) term; it is the starting point of the proof of Lemma 3.
--
--   **Formalization Note** The identity is algebraic and holds for every sample: no overlap or positivity hypothesis is needed, because $1/t$ is treated as a formal symbol on both sides (Lean's $1/0=0$ is consistent on both sides).
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, pp. 21–22, §5.1, Main Outline of the Proof of Lemma 3, display (17)

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace OfflinePolicyLearning.Regret
theorem eq17_dr_error_decomposition {X : Type*} [MeasurableSpace X] {d K n : ℕ}
    (M : Model X d) (C : CrossFit X d K) (D : Fin n → Draw X d) (πa πb : X → Fin d) :
    C.Δhat D πa πb - M.Δtilde D πa πb =
      ∑ j : Fin d,
        ((1 / n : ℝ) * ∑ i : Fin n,
            ((if πa (D i).1 = j then 1 else 0) - (if πb (D i).1 = j then 1 else 0)) *
              (C.μhatAt D i j - M.μ (D i).1 j) *
              (1 - (if (obs (D i)).2.1 = j then 1 else 0) / M.e (D i).1 j)
          + (1 / n : ℝ) * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (obs (D i)).2.1 = j),
            ((if πa (D i).1 = j then 1 else 0) - (if πb (D i).1 = j then 1 else 0)) *
              ((obs (D i)).2.2 - M.μ (D i).1 j) *
              (1 / C.ehatAt D i j - 1 / M.e (D i).1 j)
          + (1 / n : ℝ) * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (obs (D i)).2.1 = j),
            ((if πa (D i).1 = j then 1 else 0) - (if πb (D i).1 = j then 1 else 0)) *
              (M.μ (D i).1 j - C.μhatAt D i j) *
              (1 / C.ehatAt D i j - 1 / M.e (D i).1 j)) := by sorry
end OfflinePolicyLearning.Regret
