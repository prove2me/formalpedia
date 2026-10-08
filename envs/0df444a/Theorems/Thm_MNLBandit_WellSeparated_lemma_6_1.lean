-- Prove2me | Theorems.Thm_MNLBandit_WellSeparated_lemma_6_1
-- name    : MNLBandit.WellSeparated.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:26.017902+00:00
-- url     : https://prove2.me/theorems/c0f75f4c-fdfd-4710-95d7-444780295ac4
-- title:
--   Lemma 6.1, p. 20 — in a good epoch, if Tᵢ(ℓ) ≥ τ for every product offered, the offered assortment is optimal
-- statement:
--   Consider the MNL-Bandit problem under Assumption 4.1 ($0\le v_i\le v_0=1$, a feasible family $\mathcal S$ of the form (2.3) closed under subsets), with revenues $r_i\in[0,1]$, and run Algorithm 1 with any tie-breaking rule along any history of $T$ customers. Let $\Delta(\mathbf v)$ be the separation (6.1) and
--   $$
--   \tau=\frac{4NC\log NT}{\Delta^2(\mathbf v)},\qquad C=\max\{C_1^2,C_2\}.
--   $$
--   Suppose the upper confidence bounds computed at the end of epoch $\ell$ are good, and the assortment $S_{\ell+1}$ chosen from them is offered within the horizon. If every product $i\in S_{\ell+1}$ satisfies $T_i(\ell)\ge\tau$ and $T_i(\ell)\ge1$, then
--   $$
--   R(S_{\ell+1},\mathbf v)=R(S^*,\mathbf v).
--   $$
--
--   Once every product of the offered assortment has been sampled often enough, a good epoch offers an optimal assortment. Lemma 6.2 turns this into a bound on the number of good epochs that offer a sub-optimal assortment.
--
--   **Formalization Note** The page says "let $\ell$ be a good epoch and $S_\ell$ the assortment offered in epoch $\ell$". Algorithm 1 chooses an assortment from the bounds of the previous epoch, so the statement pairs the good bounds computed at the end of epoch $\ell$ with the set $S_{\ell+1}$ they select. Its proof (p. 46) uses Lemma 4.3 in the same way. "Offered in at least $\tau$ good epochs" is formalized by the lemma's own "i.e. $T_i(\ell)\ge\tau$". The extra $T_i(\ell)\ge1$ matters only when $\tau\le0$, that is when $NT\le1$, where the good-epoch bound says nothing for unsampled products. The statement is pathwise: it holds along every history of the algorithm.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 20, Lemma 6.1 (with (6.1), p. 19, and (6.2), p. 20; proof p. 46)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-- Lemma 6.1, p. 20, for Algorithm 1 under Assumption 4.1 and `r_i ∈ [0, 1]`, along any history
`h` of `T` customers: if the UCBs computed at the end of epoch `ℓ` are good, the assortment
`S_{ℓ+1}` chosen from them is offered within the horizon, and every product `i ∈ S_{ℓ+1}` has
`T_i(ℓ) ≥ τ` (and `T_i(ℓ) ≥ 1`), then `S_{ℓ+1}` is optimal: `R(S_{ℓ+1}, v) = R(S*, v)`. -/
theorem lemma_6_1 (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) (ℓ : ℕ)
    (hℓ : ℓ < epochsStarted r sel h) (hgood : IsGood v r sel h ℓ)
    (hcount : ∀ i ∈ epochSet r sel h (ℓ + 1),
      1 ≤ Tcount r sel h i ℓ ∧ tau N T (gap v r 𝒮 h𝒮) ≤ Tcount r sel h i ℓ) :
    revenue v r (epochSet r sel h (ℓ + 1)) = MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 := by sorry

end MNLBandit.WellSeparated
