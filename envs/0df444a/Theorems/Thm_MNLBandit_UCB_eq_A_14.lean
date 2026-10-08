-- Prove2me | Theorems.Thm_MNLBandit_UCB_eq_A_14
-- name    : MNLBandit.UCB.eq_A_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:53:06.11011+00:00
-- url     : https://prove2.me/theorems/0745a4ba-5f48-4137-aed8-93543472697c
-- title:
--   (A.14), p. 37 — the regret of Algorithm 1 is at most 𝔼 Σ_{ℓ≤L} (1 + V(S_ℓ))(R(S*, v) − R(S_ℓ, v))
-- statement:
--   Consider the MNL-Bandit with $N$ products, parameters $0\le v_i\le v_0=1$, revenues $r_i\in[0,1]$, a feasible family $\mathcal S$ given by totally unimodular constraints and closed under subsets, and Algorithm 1 with any argmax tie-breaking rule. For a horizon $T$, let $L$ be the number of epochs started within the first $T$ customers, $S_\ell$ the assortment of epoch $\ell$, and $V(S)=\sum_{j\in S}v_j$. Then
--   $$
--   \mathrm{Reg}_\pi(T,v)\le\mathbb E_\pi\Big\{\sum_{\ell=1}^{L}\big(1+V(S_\ell)\big)\big(R(S^*,v)-R(S_\ell,v)\big)\Big\}.
--   $$
--   The factor $1+V(S_\ell)$ is the expected length of an epoch offering $S_\ell$, so the regret, a sum over customers, is controlled by a sum over epochs; this is where the per-epoch bound of Lemma 4.3 enters.
--
--   **Formalization Note.** The paper prints (A.14) as an equality. Over a finite horizon the last epoch is cut at customer $T$ and contributes less than its expected full length, so only "$\le$" holds; the inequality is what the proof of Theorem 1 uses.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 37, (A.14)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

theorem eq_A_14 {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) :
    regret v r 𝒮 hne (alg1 r sel) T ≤
      ∑ h : History N T, histProb v (alg1 r sel) h *
        ∑ ℓ ∈ Finset.range (epochsStarted h),
          (1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
            (optRevenue v r 𝒮 hne - mnlObjective v r 1 (nextSet r sel h ℓ)) := by sorry

end MNLBandit.UCB
