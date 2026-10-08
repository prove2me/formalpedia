-- Prove2me | Theorems.Thm_MNLBandit_UCB_lemma_A_2
-- name    : MNLBandit.UCB.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:52:04.435232+00:00
-- url     : https://prove2.me/theorems/fcad1359-67ca-47a7-b243-841247807b24
-- title:
--   Lemma A.2, pp. 33–34 — concentration of the epoch averages v̄ᵢ,ℓ of Algorithm 1 (6/(Nℓ), 4/(Nℓ), 3/(Nℓ))
-- statement:
--   Consider the MNL-Bandit with $N$ products, parameters $0\le v_i\le v_0=1$, revenues $r_i\in[0,1]$, a feasible family $\mathcal S$ given by totally unimodular constraints (2.3) and closed under subsets, and Algorithm 1 run with any argmax tie-breaking rule. For an epoch index $\ell\ge1$ and a product $i$, write $T_i(\ell)$ and $\bar v_{i,\ell}$ for the number of the first $\ell$ epochs that offered $i$ and the average of their purchase counts of $i$, and $\lambda_\ell=\log(\sqrt N\ell+1)$. Then, for every horizon $T$, with probabilities over the first $T$ customers and restricted to histories in which epoch $\ell$ is completed and $T_i(\ell)\ge1$,
--   $$
--   \begin{aligned}
--   &\mathbb P_\pi\Big(|\bar v_{i,\ell}-v_i|>\sqrt{48\bar v_{i,\ell}\frac{\lambda_\ell}{T_i(\ell)}}+\frac{48\lambda_\ell}{T_i(\ell)}\Big)\le\frac{6}{N\ell},\\
--   &\mathbb P_\pi\Big(|\bar v_{i,\ell}-v_i|>\sqrt{24v_i\frac{\lambda_\ell}{T_i(\ell)}}+\frac{48\lambda_\ell}{T_i(\ell)}\Big)\le\frac{4}{N\ell},\\
--   &\mathbb P_\pi\Big(\bar v_{i,\ell}>\frac{3v_i}{2}+\frac{48\lambda_\ell}{T_i(\ell)}\Big)\le\frac{3}{N\ell}.
--   \end{aligned}
--   $$
--   These bounds are the probabilistic core of the upper confidence bounds (3.4): they give Lemma 4.1 directly.
--
--   **Formalization Note.**
--   1. The paper prints $48\log(\ell+1)/T_i(\ell)$ as the second term of the first bound; its proof (Corollary D.1 and (D.22)) and every use ((A.4)–(A.5)) have $48\log(\sqrt N\ell+1)/T_i(\ell)$, which is stated here.
--   2. $\bar v_{i,\ell}$ is undefined when $T_i(\ell)=0$; the events require $T_i(\ell)\ge1$.
--   3. The paper's statement is for the infinite-horizon process ("for every epoch $\ell$"). Here it is stated for every finite horizon $T$, on the event that epoch $\ell$ has been completed by customer $T$; uniformity in $T$ is the infinite-horizon statement.
--   4. The standing assumptions of §4 (TU and down-closed $\mathcal S$, $r_i\in[0,1]$) are carried as hypotheses.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, pp. 33–34, Lemma A.2 (proof p. 56)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

theorem lemma_A_2 {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) (i : Fin N) :
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
        |vbar r sel h i ℓ - v i| >
          Real.sqrt (48 * vbar r sel h i ℓ * Real.log (Real.sqrt N * ℓ + 1)
              / Tcount r sel h i ℓ)
            + 48 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
        ≤ 6 / (N * ℓ) ∧
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
        |vbar r sel h i ℓ - v i| >
          Real.sqrt (24 * v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
            + 48 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
        ≤ 4 / (N * ℓ) ∧
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
        vbar r sel h i ℓ >
          3 * v i / 2 + 48 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
        ≤ 3 / (N * ℓ) := by sorry

end MNLBandit.UCB
