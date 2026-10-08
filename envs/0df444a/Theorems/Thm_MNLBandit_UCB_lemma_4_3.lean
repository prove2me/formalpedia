-- Prove2me | Theorems.Thm_MNLBandit_UCB_lemma_4_3
-- name    : MNLBandit.UCB.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:52:23.69071+00:00
-- url     : https://prove2.me/theorems/645f36a5-88d5-495c-8a70-2419b0a2b941
-- title:
--   Lemma 4.3, p. 14 — (1 + V(S_{ℓ+1}))(R̃_{ℓ+1}(S_{ℓ+1}) − R(S_{ℓ+1}, v)) ≤ Σᵢ[C₁√(vᵢ log(√Nℓ+1)/Tᵢ(ℓ)) + C₂ log(√Nℓ+1)/Tᵢ(ℓ)] w.p. ≥ 1 − 13/ℓ
-- statement:
--   Consider the MNL-Bandit with $N$ products, parameters $0\le v_i\le v_0=1$, revenues $r_i\in[0,1]$, a feasible family $\mathcal S$ given by totally unimodular constraints and closed under subsets, and Algorithm 1 with any argmax tie-breaking rule. Let $\ell\ge1$, $\lambda_\ell=\log(\sqrt N\ell+1)$, $C_1=\sqrt{72}+\sqrt{24}$ and $C_2=144$. Let $S_{\ell+1}$ be the assortment computed at the end of epoch $\ell$ and $\tilde R_{\ell+1}$ the optimistic revenue built from $v^{\mathrm{UCB}}_{\cdot,\ell}$. For every horizon $T$, with probabilities restricted to histories in which epoch $\ell$ is completed by customer $T$ and every product of $S_{\ell+1}$ has $T_i(\ell)\ge1$,
--   $$
--   \Big(1+\sum_{j\in S_{\ell+1}}v_j\Big)\big(\tilde R_{\ell+1}(S_{\ell+1})-R(S_{\ell+1},v)\big)\le\sum_{i\in S_{\ell+1}}\Big(C_1\sqrt{\frac{v_i\lambda_\ell}{T_i(\ell)}}+C_2\frac{\lambda_\ell}{T_i(\ell)}\Big)
--   $$
--   with probability at least $1-\frac{13}{\ell}$. This per-epoch rate is summed over epochs in the proof of Theorem 1.
--
--   **Formalization Note.**
--   1. *Sum over $i$.* The page's right-hand side has a free index $i$; its proof ((A.11)–(A.12), p. 36) gives the sum over $i\in S_\ell$, which is stated.
--   2. *Index reading.* As in Lemma 4.2, the page's $\tilde R_\ell(S_\ell)$ with $v^{\mathrm{UCB}}_{i,\ell}$, $T_i(\ell)$ and $1-13/\ell$ is read as the estimate built at the end of epoch $\ell$.
--   3. *Constants.* "There exist constants $C_1$ and $C_2$" is instantiated with the values of Lemma 4.1's proof.
--   4. *Guard.* The right side divides by $T_i(\ell)$, so the event requires $T_i(\ell)\ge1$ for every $i\in S_{\ell+1}$.
--   5. Finite horizon $T$ as in Lemma A.2.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 14, Lemma 4.3 (proof p. 36, (A.11)–(A.12))

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

theorem lemma_4_3 {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧
        (∀ i ∈ nextSet r sel h ℓ, 1 ≤ Tcount r sel h i ℓ) ∧
        ¬ ((1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
              (mnlObjective (fun j => vUCB r sel h j ℓ) r 1 (nextSet r sel h ℓ)
                - mnlObjective v r 1 (nextSet r sel h ℓ)) ≤
            ∑ i ∈ nextSet r sel h ℓ,
              ((Real.sqrt 72 + Real.sqrt 24)
                  * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
                + 144 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)))
      ≤ 13 / ℓ := by sorry

end MNLBandit.UCB
