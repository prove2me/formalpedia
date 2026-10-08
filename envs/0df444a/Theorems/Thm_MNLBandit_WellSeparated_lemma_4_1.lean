-- Prove2me | Theorems.Thm_MNLBandit_WellSeparated_lemma_4_1
-- name    : MNLBandit.WellSeparated.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:17.677337+00:00
-- url     : https://prove2.me/theorems/b269494a-114c-4fab-a593-11764892c703
-- title:
--   Lemma 4.1, p. 13 — v^UCB_{i,ℓ} ≥ vᵢ w.p. ≥ 1 − 6/(Nℓ), and its convergence rate w.p. ≥ 1 − 7/(Nℓ)
-- statement:
--   Consider the MNL-Bandit problem with $N$ products, attraction parameters $0\le v_i\le v_0=1$, revenues $r_i\in[0,1]$, and a feasible family $\mathcal S$ of the form (2.3) that is closed under subsets (Assumption 4.1). Run Algorithm 1 with any tie-breaking rule. Let $v^{\mathrm{UCB}}_{i,\ell}$ be the upper confidence bound (3.4) computed at the end of epoch $\ell$, and $T_i(\ell)$ the number of epochs $\tau\le\ell$ that offered product $i$.
--
--   For every epoch $\ell\ge1$ and every product $i$:
--
--   1. $v^{\mathrm{UCB}}_{i,\ell}\ge v_i$ with probability at least $1-\dfrac{6}{N\ell}$;
--   2. with $C_1=\sqrt{72}+\sqrt{24}$ and $C_2=144$,
--   $$
--   v^{\mathrm{UCB}}_{i,\ell}-v_i\le C_1\sqrt{\frac{v_i\log(\sqrt N\ell+1)}{T_i(\ell)}}+C_2\frac{\log(\sqrt N\ell+1)}{T_i(\ell)}
--   $$
--   with probability at least $1-\dfrac{7}{N\ell}$.
--
--   The lemma says the upper confidence bounds are optimistic and converge to the true parameters at the stated rate. In the well-separated analysis it shows that every epoch is "good" with probability at least $1-13/\ell$.
--
--   **Formalization Note** The model has a finite horizon $T$. Each part is stated for every $T$ as an upper bound on the probability that epoch $\ell$ is completed within the first $T$ customers and the bound fails; uniformity in $T$ is the infinite-horizon statement. Part 2 is stated on the event $T_i(\ell)\ge1$, where the right-hand side is defined. The paper's "there exist constants $C_1$ and $C_2$" is instantiated with the values its proof establishes (p. 35). This is the same statement as in the companion mission on Theorem 1, restated here because the two missions are drafted independently.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 13, Lemma 4.1 (constants C₁, C₂ from p. 35, last display before Lemma A.3)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-- Lemma 4.1, p. 13, for Algorithm 1 under Assumption 4.1: for every epoch `ℓ ≥ 1` and product
`i`, (1) `v^UCB_{i,ℓ} < v_i` with probability at most `6/(Nℓ)`, and (2) the deviation bound with
`C₁ = √72 + √24`, `C₂ = 144` fails (while `T_i(ℓ) ≥ 1`) with probability at most `7/(Nℓ)`; both
on the event that epoch `ℓ` is completed within the first `T` customers, for every `T`. -/
theorem lemma_4_1 (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) (i : Fin N) :
    probT v (alg1 r sel) T
        (fun h => ℓ ≤ epochsDone r sel h ∧ vUCB r sel h i ℓ < v i)
      ≤ 6 / ((N : ℝ) * ℓ) ∧
    probT v (alg1 r sel) T
        (fun h => ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
          C₁ * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
            + C₂ * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ
            < vUCB r sel h i ℓ - v i)
      ≤ 7 / ((N : ℝ) * ℓ) := by sorry

end MNLBandit.WellSeparated
