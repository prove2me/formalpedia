-- Prove2me | Theorems.Thm_MNLBandit_WellSeparated_lemma_4_3
-- name    : MNLBandit.WellSeparated.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:10:27.053492+00:00
-- url     : https://prove2.me/theorems/08fb0f94-f4c0-4a78-990b-9eb4a3d50a96
-- title:
--   Lemma 4.3, p. 14 — (1 + Σ_{j∈S_ℓ} v_j)(R̃_ℓ(S_ℓ) − R(S_ℓ, v)) ≤ Σᵢ [C₁√(vᵢ log(√Nℓ+1)/Tᵢ(ℓ)) + C₂ log(√Nℓ+1)/Tᵢ(ℓ)] w.p. ≥ 1 − 13/ℓ
-- statement:
--   Consider the MNL-Bandit problem under Assumption 4.1 ($0\le v_i\le v_0=1$, a feasible family of the form (2.3) closed under subsets), with revenues $r_i\in[0,1]$, and run Algorithm 1 with any tie-breaking rule. After epoch $\ell$, the algorithm computes the upper confidence bounds $v^{\mathrm{UCB}}_{i,\ell}$ and offers in the next epoch
--   $$
--   S_{\ell+1}\in\arg\max_{S\in\mathcal S}\tilde R_{\ell+1}(S),\qquad \tilde R_{\ell+1}(S)=\frac{\sum_{i\in S}r_iv^{\mathrm{UCB}}_{i,\ell}}{1+\sum_{j\in S}v^{\mathrm{UCB}}_{j,\ell}}.
--   $$
--   Let $C_1=\sqrt{72}+\sqrt{24}$ and $C_2=144$. For every epoch $\ell\ge1$, with probability at least $1-\dfrac{13}{\ell}$,
--   $$
--   \Big(1+\sum_{j\in S_{\ell+1}}v_j\Big)\big(\tilde R_{\ell+1}(S_{\ell+1})-R(S_{\ell+1},\mathbf v)\big)\le\sum_{i\in S_{\ell+1}}\left(C_1\sqrt{\frac{v_i\log(\sqrt N\ell+1)}{T_i(\ell)}}+C_2\frac{\log(\sqrt N\ell+1)}{T_i(\ell)}\right).
--   $$
--
--   This is the per-epoch convergence rate of the optimistic revenue estimate to the true revenue of the offered assortment. Lemma 6.1 starts from it.
--
--   **Formalization Note** Three readings are disclosed:
--
--   1. The printed right-hand side has a free index $i$; its proof ((A.11)–(A.12), p. 36) gives the sum over $i\in S_\ell$, which is stated.
--   2. The printed statement writes $\tilde R_\ell(S_\ell)$ together with $T_i(\ell)$ and $\log(\sqrt N\ell+1)$. Algorithm 1 builds $\tilde R_\ell$ from the bounds of epoch $\ell-1$. The statement uses the consistent reading: the estimate built at the end of epoch $\ell$, which selects $S_{\ell+1}$.
--   3. The event is restricted to $T_i(\ell)\ge1$ for every $i\in S_{\ell+1}$, where the right-hand side is defined.
--
--   The probability is that of epoch $\ell$ being completed within the first $T$ customers with the inequality failing, for every horizon $T$. The constants are the values from the proof of Lemma 4.1 (p. 35). The same statement appears in the companion mission on Theorem 1.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 14, Lemma 4.3 (sum over i ∈ S_ℓ from (A.11)–(A.12), p. 36; constants from p. 35)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-- Lemma 4.3, p. 14, for Algorithm 1 under Assumption 4.1 and `r_i ∈ [0, 1]`: with `S = S_{ℓ+1}`
the assortment chosen from the UCBs computed at the end of epoch `ℓ ≥ 1`,
`(1 + ∑_{j∈S} v_j)(R̃_{ℓ+1}(S) − R(S, v)) ≤ ∑_{i∈S} [C₁ √(v_i log(√Nℓ+1)/T_i(ℓ)) + C₂ log(√Nℓ+1)/T_i(ℓ)]`
fails, on the event that epoch `ℓ` is completed within `T` customers and every `i ∈ S` has
`T_i(ℓ) ≥ 1`, with probability at most `13/ℓ`, for every `T`. -/
theorem lemma_4_3 (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    probT v (alg1 r sel) T
        (fun h => ℓ ≤ epochsDone r sel h ∧
          (∀ i ∈ epochSet r sel h (ℓ + 1), 1 ≤ Tcount r sel h i ℓ) ∧
          ∑ i ∈ epochSet r sel h (ℓ + 1),
              (C₁ * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
                + C₂ * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
            < (1 + ∑ j ∈ epochSet r sel h (ℓ + 1), v j) *
                (mnlObjective (fun j => vUCB r sel h j ℓ) r 1 (epochSet r sel h (ℓ + 1))
                  - revenue v r (epochSet r sel h (ℓ + 1))))
      ≤ 13 / (ℓ : ℝ) := by sorry

end MNLBandit.WellSeparated
