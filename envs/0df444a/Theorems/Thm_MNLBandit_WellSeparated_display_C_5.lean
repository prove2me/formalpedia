-- Prove2me | Theorems.Thm_MNLBandit_WellSeparated_display_C_5
-- name    : MNLBandit.WellSeparated.display_C_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:27.146863+00:00
-- url     : https://prove2.me/theorems/5aa8cde3-3731-4801-bf71-5a64e9b34d58
-- title:
--   (C.5), p. 48 — Reg_π(T, v) ≤ 𝔼_π Σ_{ℓ=1}^L (1 + V(S_ℓ))(R(S*, v) − R(S_ℓ, v))
-- statement:
--   Consider the MNL-Bandit problem under Assumption 4.1 with revenues $r_i\in[0,1]$, and run Algorithm 1 with any tie-breaking rule. Let $L$ be the number of epochs started within the first $T$ customers, $S_\ell$ the assortment of epoch $\ell$, and $V(S)=\sum_{j\in S}v_j$. Then
--   $$
--   \mathrm{Reg}_\pi(T,\mathbf v)\le\mathbb E_\pi\Big[\sum_{\ell=1}^{L}\big(1+V(S_\ell)\big)\big(R(S^*,\mathbf v)-R(S_\ell,\mathbf v)\big)\Big].
--   $$
--
--   Given its assortment, the length of an epoch is geometric with mean $1+V(S_\ell)$. The display rewrites the per-customer regret as a per-epoch regret, the form in which the epoch-wise bounds of Lemmas 4.3, 6.2 and Corollary C.1 apply.
--
--   **Formalization Note** The paper writes "$=$". With a finite horizon the last epoch is cut at time $T$, so it contributes at most its expected full length. Only "$\le$" holds, and this is all the proof of Theorem 3 uses. The expectation is over histories of length $T$, a finite sum.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 48, (C.5) (the same rewriting as (A.14), p. 37)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-- Display (C.5), p. 48 (the epoch rewriting of the regret, as an inequality), for Algorithm 1
under Assumption 4.1 and `r_i ∈ [0, 1]`:
`Reg_π(T, v) ≤ 𝔼_π ∑_{ℓ=1}^{L} (1 + V(S_ℓ))(R(S*, v) − R(S_ℓ, v))`, `V(S) = ∑_{j∈S} v_j`, where `L`
is the number of epochs started within the first `T` customers. -/
theorem display_C_5 (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel) (T : ℕ) :
    MNLBandit.UCB.regret v r 𝒮 h𝒮 (alg1 r sel) T ≤
      ∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h *
        ∑ ℓ ∈ Finset.Icc 1 (epochsStarted r sel h),
          (1 + ∑ j ∈ epochSet r sel h ℓ, v j) *
            (MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 - revenue v r (epochSet r sel h ℓ)) := by sorry

end MNLBandit.WellSeparated
