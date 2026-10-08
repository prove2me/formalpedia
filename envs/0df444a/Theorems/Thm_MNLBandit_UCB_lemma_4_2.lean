-- Prove2me | Theorems.Thm_MNLBandit_UCB_lemma_4_2
-- name    : MNLBandit.UCB.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:52:12.770459+00:00
-- url     : https://prove2.me/theorems/75c50815-9981-4011-b5df-1232c1d63bdd
-- title:
--   Lemma 4.2, p. 13 — R̃_{ℓ+1}(S_{ℓ+1}) ≥ R̃_{ℓ+1}(S*) ≥ R(S*, v) w.p. ≥ 1 − 6/ℓ
-- statement:
--   Consider the MNL-Bandit with $N$ products, parameters $0\le v_i\le v_0=1$, revenues $r_i\in[0,1]$, a feasible family $\mathcal S$ given by totally unimodular constraints and closed under subsets, and Algorithm 1 with any argmax tie-breaking rule. Let $S^*\in\mathcal S$ be an assortment with the highest expected revenue, $R(S^*,v)=\max_{S\in\mathcal S}R(S,v)$, all of whose products have $v_j>0$. Let $\ell\ge1$. After epoch $\ell$ the algorithm computes $v^{\mathrm{UCB}}_{\cdot,\ell}$, the optimistic revenue $\tilde R_{\ell+1}(S)=\sum_{i\in S}r_iv^{\mathrm{UCB}}_{i,\ell}/(1+\sum_{j\in S}v^{\mathrm{UCB}}_{j,\ell})$ and the next assortment $S_{\ell+1}$. For every horizon $T$, with probabilities restricted to histories in which epoch $\ell$ is completed by customer $T$,
--   $$
--   \tilde R_{\ell+1}(S_{\ell+1})\ge\tilde R_{\ell+1}(S^*)\ge R(S^*,v)\qquad\text{with probability at least }1-\frac{6}{\ell}.
--   $$
--   In words, the optimistic estimate of the chosen assortment upper-bounds the optimal expected revenue with high probability.
--
--   **Formalization Note.**
--   1. *Index reading.* The page writes $\tilde R_\ell(S_\ell)$ with probability $1-6/\ell$, while its proof ((A.9)–(A.10)) uses $v^{\mathrm{UCB}}_{i,\ell}$, which by (3.7) and Algorithm 1 belongs to $\tilde R_{\ell+1}$ and $S_{\ell+1}$. The statement uses the estimate built at the end of epoch $\ell$.
--   2. *Positivity on $S^*$.* The page's "the assortment with highest expected revenue" is read as an optimal assortment containing no product with $v_j=0$; such an optimum always exists (removing products with $v_j=0$ keeps the revenue and, by closure under subsets, feasibility). For an optimum containing a product with $v_j=0$, the middle inequality can fail with high probability (see Lemma A.3's note).
--   3. Finite horizon $T$ and the event "epoch $\ell$ completed", as in Lemma A.2.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 13, Lemma 4.2 (proof p. 36, (A.9)–(A.10))

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

theorem lemma_4_2 {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (Sstar : Finset (Fin N)) (hSstar : Sstar ∈ 𝒮)
    (hopt : mnlObjective v r 1 Sstar = optRevenue v r 𝒮 hne)
    (hpos : ∀ j ∈ Sstar, 0 < v j)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧
        ¬ (mnlObjective (fun j => vUCB r sel h j ℓ) r 1 (nextSet r sel h ℓ) ≥
              mnlObjective (fun j => vUCB r sel h j ℓ) r 1 Sstar ∧
            mnlObjective (fun j => vUCB r sel h j ℓ) r 1 Sstar ≥ mnlObjective v r 1 Sstar))
      ≤ 6 / ℓ := by sorry

end MNLBandit.UCB
