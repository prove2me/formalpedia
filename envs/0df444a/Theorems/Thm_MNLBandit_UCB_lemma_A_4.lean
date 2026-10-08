-- Prove2me | Theorems.Thm_MNLBandit_UCB_lemma_A_4
-- name    : MNLBandit.UCB.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:09:56.205754+00:00
-- url     : https://prove2.me/theorems/f8bd19a7-e94b-4005-b889-b48ee9a1ac4c
-- title:
--   Lemma A.4, p. 36 — R̃(S) − R(S, v) ≤ Σ_{j∈S}(v^UCB_j − v_j)/(1 + Σ_{j∈S} v_j)
-- statement:
--   Let $r_i\in[0,1]$ be revenues, $S$ an assortment, and $v,u$ parameter vectors with $0\le v_i\le u_i$ for every $i\in S$. Then
--   $$
--   R(S,u)-R(S,v)\le\frac{\sum_{j\in S}(u_j-v_j)}{1+\sum_{j\in S}v_j},\qquad R(S,v)=\frac{\sum_{i\in S}r_iv_i}{1+\sum_{j\in S}v_j}.
--   $$
--   In the paper $u=v^{\mathrm{UCB}}_{\cdot,\ell}$, so $R(S_\ell,u)=\tilde R_\ell(S_\ell)$ and the lemma bounds the overestimate of the revenue of the offered assortment by the total error of the parameter estimates on it. It is a Lipschitz property of the MNL revenue.
--
--   **Formalization Note.** The statement is the page's, with $v^{\mathrm{UCB}}_{\cdot,\ell}$ replaced by an arbitrary dominating vector $u$; the epoch index plays no role in the lemma.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 36, Lemma A.4

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

theorem lemma_A_4 {N : ℕ} (r : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (v u : Fin N → ℝ) (S : Finset (Fin N)) (hv : ∀ i ∈ S, 0 ≤ v i)
    (hvu : ∀ i ∈ S, v i ≤ u i) :
    mnlObjective u r 1 S - mnlObjective v r 1 S ≤
      (∑ j ∈ S, (u j - v j)) / (1 + ∑ j ∈ S, v j) := by sorry

end MNLBandit.UCB
