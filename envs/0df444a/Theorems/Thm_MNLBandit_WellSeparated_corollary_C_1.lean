-- Prove2me | Theorems.Thm_MNLBandit_WellSeparated_corollary_C_1
-- name    : MNLBandit.WellSeparated.corollary_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:37.897995+00:00
-- url     : https://prove2.me/theorems/ee4d2c6a-74b8-4d47-8744-605dd148c4e2
-- title:
--   Corollary C.1, p. 48 — at most N log NT epochs offer a product with Tᵢ(ℓ) < log NT
-- statement:
--   Consider the MNL-Bandit problem under Assumption 4.1 with revenues $r_i\in[0,1]$, and run Algorithm 1 with any tie-breaking rule along any history of $T$ customers. Let $S_1,\dots,S_L$ be the assortments of the epochs started within the horizon. Let $T_i(\ell)=|\{\tau\le\ell : i\in S_\tau\}|$ be the number of epochs up to and including $\ell$ that offered product $i$ (3.2). Then
--   $$
--   \Big|\big\{\ell\in\{1,\dots,L\} : T_i(\ell)<\log NT\ \text{for some } i\in S_\ell\big\}\Big|\le N\log NT.
--   $$
--
--   In the proof of Theorem 3 this bounds the regret of the epochs in which some offered product has been sampled fewer than $\log NT$ times by $N(N+1)\log NT$.
--
--   **Formalization Note** The count uses the paper's own indexing: $T_i(\ell)$ includes epoch $\ell$, and $S_\ell$ is the set offered in epoch $\ell$. The last epoch is counted even if it is still in progress at time $T$. The statement is pathwise.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 48, Corollary C.1

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-- Corollary C.1, p. 48, for Algorithm 1 under Assumption 4.1 and `r_i ∈ [0, 1]`, along any
history `h` of `T` customers: the number of epochs `ℓ = 1, …, L` started within the horizon whose
assortment `S_ℓ` contains a product `i` with `T_i(ℓ) < log NT` (`T_i(ℓ)` counting the epochs
`τ ≤ ℓ`, epoch `ℓ` included, that offered `i`) is at most `N log NT`. -/
theorem corollary_C_1 (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) :
    (((Finset.Icc 1 (epochsStarted r sel h)).filter (fun ℓ =>
        ∃ i ∈ epochSet r sel h ℓ, (Tcount r sel h i ℓ : ℝ) < Real.log (N * T))).card : ℝ)
      ≤ N * Real.log (N * T) := by sorry

end MNLBandit.WellSeparated
