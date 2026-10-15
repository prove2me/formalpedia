-- Prove2me | Theorems.Thm_LinExchangeSP_ZPlus_lemma_7_2
-- name    : LinExchangeSP.ZPlus.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:28.502206+00:00
-- url     : https://prove2.me/theorems/d2fd955a-b742-4354-94c7-36cc7e9ea8ac
-- title:
--   Lemma 7.2, p. 16 — Gaussian elimination on a Z₊-matrix: T′ = YT, Y ≥ 0, T′ upper triangular with 0/1 diagonal
-- statement:
--   Let $T \in \mathcal{Z}_+(\ell,t)$ be a $Z_+$-matrix and let $(Y, T')$ be the output of the Gaussian elimination of the proof of Lemma 7.2 (step $k$: if the pivot $T^{(k-1)}_{kk}$ is nonzero, divide row $k$ by it and add $-T^{(k-1)}_{ik}/T^{(k-1)}_{kk}$ times row $k$ to every row $i > k$; $Y$ records the row operations). Then:
--
--   1. $T' = YT$;
--   2. every entry of $Y \in \mathbb{Q}^{\ell\times\ell}$ is nonnegative;
--   3. $T'$ is upper triangular: $T'_{ij} = 0$ for $j < i$;
--   4. every diagonal entry of $T'$ is $0$ or $1$;
--   5. every off-diagonal entry of $T'$ is nonpositive;
--   6. if $T_{ik} < 0$ for some $k \in [t]$ and $i \in [k+1,\ell]$, then $T'_{kk} = 1$:
--   $$T_{ik} < 0 \text{ for some } i > k \ \Longrightarrow\ T'_{kk} = 1.$$
--
--   Gaussian elimination on a $Z_+$-matrix thus only adds nonnegative multiples of rows to other rows. This is what lets the proof of Theorem 6.4 derive valid two-variable constraints for $P_M$ from $M\bar p \ge -\lambda$ and $M\bar p \le \gamma$.
--
--   **Formalization Note** The statement is about the specific elimination procedure of the paper's proof (p. 17), defined in the construction module, not about the existence of some $Y \ge 0$: the existential form would be nearly trivial ($Y = 0$ meets every clause but the last). The paper writes $T' \in \mathbb{R}^{\ell\times t}$, $Y \in \mathbb{R}^{\ell\times\ell}$; for rational $T$ the elimination stays rational and is computed in $\mathbb{Q}$. Indices are 0-based.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 16, Lemma 7.2 (proof p. 17)

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting
import Definitions.Def_LinExchangeSP_ZPlus_Construction

namespace LinExchangeSP.ZPlus

/-- Lemma 7.2 (p. 16), about the output `(Y, T') = gaussElim T` of the elimination of its proof
(p. 17): `T' = YT`, `Y ≥ 0` entrywise, `T'` is upper triangular with diagonal entries `0` or `1`
and nonpositive off-diagonal entries, and `T'_kk = 1` whenever `T_ik < 0` for some `i > k`.
Indices are 0-based. -/
theorem lemma_7_2 {l t : ℕ} (T : Matrix (Fin l) (Fin t) ℚ) (hT : IsZPlus T) :
    (gaussElim T).2 = (gaussElim T).1 * T ∧
    (∀ i j, 0 ≤ (gaussElim T).1 i j) ∧
    (∀ (i : Fin l) (j : Fin t), (j : ℕ) < (i : ℕ) → (gaussElim T).2 i j = 0) ∧
    (∀ (i : Fin l) (j : Fin t), (i : ℕ) = (j : ℕ) →
      (gaussElim T).2 i j = 0 ∨ (gaussElim T).2 i j = 1) ∧
    (∀ (i : Fin l) (j : Fin t), (i : ℕ) ≠ (j : ℕ) → (gaussElim T).2 i j ≤ 0) ∧
    (∀ (k : Fin t) (i : Fin l), (k : ℕ) < (i : ℕ) → T i k < 0 →
      ∀ hk : (k : ℕ) < l, (gaussElim T).2 ⟨k, hk⟩ k = 1) := by sorry

end LinExchangeSP.ZPlus
