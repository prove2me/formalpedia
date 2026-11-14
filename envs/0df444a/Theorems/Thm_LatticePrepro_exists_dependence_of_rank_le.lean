-- Prove2me | Theorems.Thm_LatticePrepro_exists_dependence_of_rank_le
-- name    : LatticePrepro.exists_dependence_of_rank_le
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:24:56.018406+00:00
-- url     : https://prove2.me/theorems/a7a91562-81b9-46b1-820a-192b4d7b328e
-- title:
--   A square matrix of rank at most $t$ has linearly dependent first $t+1$ columns
-- statement:
--   Let $K$ be a field, $\ell$ a natural number, and $A = (A_{ij})_{0 \le i,j < \ell}$ a square matrix over $K$. If $\operatorname{rank} A \le t$ and $t + 1 \le \ell$, then the first $t+1$ columns of $A$ are linearly dependent: there is a nonzero vector $c = (c_0, \dots, c_t) \in K^{t+1}$ with
--   $$\sum_{j=0}^{t} c_j\, A_{i,j} = 0 \qquad (0 \le i < \ell).$$
--
--   In the soundness part of Theorem A.8 (the polynomial evaluation tables form a moment representation), this is applied to the Hankel matrix $(\hat M_{h+h'}(y))_{0\le h,h'<\ell}$ formed by the moment maps $\hat M_k$ evaluated at an evaluation table $y$, whose rank $\rho$ is small. The resulting dependence among its first $\rho + 1$ columns is the linear recurrence from which Theorem A.7 reconstructs a sparse coefficient function.
--
--   **Formalization Note**: Rows and columns are indexed by `Fin ℓ`; a column index $j \in \{0,\dots,t\}$ is embedded into $\{0, \dots, \ell-1\}$ by `Fin.castLE`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), auxiliary lemma used in the proof of Theorem A.8 (\label{thm:moment-representation-construction}), where it supplies the column dependence required by Theorem A.7 (\label{thm:moment-hankel-reconstruction}); Lean: LatticePrepro/Basic/Matrix.lean, LatticePrepro.exists_dependence_of_rank_le

import Mathlib

open Polynomial Matrix

theorem LatticePrepro.exists_dependence_of_rank_le {K : Type*} [Field K] {ℓ : ℕ} (A : Matrix (Fin ℓ) (Fin ℓ) K)
    {t : ℕ} (ht : A.rank ≤ t) (htℓ : t + 1 ≤ ℓ) :
    ∃ c : Fin (t + 1) → K, c ≠ 0 ∧ ∀ i : Fin ℓ, ∑ j, c j * A i (Fin.castLE htℓ j) = 0 := by sorry
