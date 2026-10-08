-- Prove2me | Theorems.Thm_MNLBandit_WellSeparated_lemma_6_2
-- name    : MNLBandit.WellSeparated.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:33.95371+00:00
-- url     : https://prove2.me/theorems/6ebdf9a8-9baa-455c-ad6b-8a7d87e09a91
-- title:
--   Lemma 6.2, p. 20 — Algorithm 1 offers sub-optimal assortments in at most Nτ good epochs
-- statement:
--   Consider the MNL-Bandit problem under Assumption 4.1 ($0\le v_i\le v_0=1$, a feasible family $\mathcal S$ of the form (2.3) closed under subsets), with revenues $r_i\in[0,1]$, and run Algorithm 1 with any tie-breaking rule along any history of $T$ customers. Let $\tau=4NC\log NT/\Delta^2(\mathbf v)$ as in (6.2), and let $L$ be the number of epochs started within the horizon. Then
--   $$
--   \Big|\big\{\ell\in\{0,\dots,L-1\} : \text{epoch }\ell\text{ is good and }R(S_{\ell+1},\mathbf v)<R(S^*,\mathbf v)\big\}\Big|\le N\tau.
--   $$
--   In words: Algorithm 1 cannot offer sub-optimal assortments in more than $N\tau$ good epochs.
--
--   Together with the fact that bad epochs are rare, this bounds the number of epochs in which the algorithm loses revenue. This is the step that gives the logarithmic dependence on $T$ in Theorem 3.
--
--   **Formalization Note** As in Lemma 6.1, a good epoch $\ell$ is paired with the assortment $S_{\ell+1}$ selected by its upper confidence bounds. Epoch $\ell=0$ (the first assortment, chosen from $v^{\mathrm{UCB}}_{i,0}=1$) is included in the count. The bound is pathwise: it holds along every history.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 20, Lemma 6.2 (proof pp. 46–47, (C.2)–(C.4))

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

open Classical in
/-- Lemma 6.2, p. 20, for Algorithm 1 under Assumption 4.1 and `r_i ∈ [0, 1]`, along any history
`h` of `T` customers: among the epochs started within the horizon, at most `Nτ` are good epochs
offering a sub-optimal assortment (epoch `ℓ + 1` counted when the UCBs computed at the end of
epoch `ℓ` are good and `R(S_{ℓ+1}, v) < R(S*, v)`). -/
theorem lemma_6_2 (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) :
    (((Finset.range (epochsStarted r sel h)).filter (fun ℓ =>
        IsGood v r sel h ℓ ∧
          revenue v r (epochSet r sel h (ℓ + 1)) < MNLBandit.UCB.optRevenue v r 𝒮 h𝒮)).card : ℝ)
      ≤ N * tau N T (gap v r 𝒮 h𝒮) := by sorry

end MNLBandit.WellSeparated
