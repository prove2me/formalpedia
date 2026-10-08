-- Prove2me | Theorems.Thm_MNLBandit_UCB_lemma_4_1
-- name    : MNLBandit.UCB.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:52:01.987993+00:00
-- url     : https://prove2.me/theorems/8bdd75aa-258d-48cf-9fb9-7451ced19e6f
-- title:
--   Lemma 4.1, p. 13 — v^UCB_{i,ℓ} ≥ vᵢ w.p. ≥ 1 − 6/(Nℓ), and its convergence rate w.p. ≥ 1 − 7/(Nℓ)
-- statement:
--   Consider the MNL-Bandit with $N$ products, parameters $0\le v_i\le v_0=1$, revenues $r_i\in[0,1]$, a feasible family $\mathcal S$ given by totally unimodular constraints and closed under subsets, and Algorithm 1 with any argmax tie-breaking rule. Let $\ell\ge1$, let $i$ be a product, and write $\lambda_\ell=\log(\sqrt N\ell+1)$. For every horizon $T$, with probabilities restricted to histories in which epoch $\ell$ is completed by customer $T$:
--   1. the upper confidence bound is optimistic,
--   $$
--   \mathbb P_\pi\big(v^{\mathrm{UCB}}_{i,\ell}<v_i\big)\le\frac{6}{N\ell};
--   $$
--   2. with $C_1=\sqrt{72}+\sqrt{24}$ and $C_2=144$, on the event $T_i(\ell)\ge1$,
--   $$
--   \mathbb P_\pi\Big(v^{\mathrm{UCB}}_{i,\ell}-v_i>C_1\sqrt{\frac{v_i\lambda_\ell}{T_i(\ell)}}+C_2\frac{\lambda_\ell}{T_i(\ell)}\Big)\le\frac{7}{N\ell}.
--   $$
--   Optimism (part 1) drives Lemma 4.2 and the convergence rate (part 2) drives Lemma 4.3.
--
--   **Formalization Note.**
--   1. The lemma says "there exist constants $C_1$ and $C_2$"; the values $\sqrt{72}+\sqrt{24}$ and $144$ are those its proof establishes (p. 35, last display before Lemma A.3), a disclosed instantiation of the existential.
--   2. Part 2 needs $T_i(\ell)\ge1$ (the right side divides by it). Part 1 needs no such guard: while $T_i(\ell)=0$ the algorithm keeps $v^{\mathrm{UCB}}_{i,\ell}=1\ge v_i$.
--   3. Finite horizon $T$ and the event "epoch $\ell$ completed" as in Lemma A.2; uniformity in $T$ is the paper's statement.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 13, Lemma 4.1 (proof pp. 34–35)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

theorem lemma_4_1 {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) (i : Fin N) :
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧ vUCB r sel h i ℓ < v i) ≤ 6 / (N * ℓ) ∧
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
        vUCB r sel h i ℓ - v i >
          (Real.sqrt 72 + Real.sqrt 24)
              * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
            + 144 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
        ≤ 7 / (N * ℓ) := by sorry

end MNLBandit.UCB
