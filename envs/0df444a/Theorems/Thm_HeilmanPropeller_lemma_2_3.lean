-- Prove2me | Theorems.Thm_HeilmanPropeller_lemma_2_3
-- name    : HeilmanPropeller.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:19.494201+00:00
-- url     : https://prove2.me/theorems/973f2993-39f0-4d44-bf75-3dae1eea3e51
-- title:
--   Lemma 2.3: the probabilistic form at level $k$
-- statement:
--   Throughout, $\gamma_n$ is the standard Gaussian measure on $\mathbb R^n$ (Euclidean norm), and for a partition $\mathcal A=(A_1,\dots,A_k)$ the Gaussian moments, cell measures and value are
--
--   $$z_i=\int_{A_i}x\,d\gamma_n(x),\qquad p_i=\gamma_n(A_i),\qquad F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2 .$$
--
--   $C_k=\sup_{n\ge1}\sup_{\mathcal A}F(\mathcal A)$, the supremum over partitions of $\mathbb R^n$ into $k$ sets (display (1.1)).
--
--   Let $k\ge1$ and $G\sim\gamma_{k-1}$. For any $v_1,\dots,v_k\in\mathbb R^{k-1}$,
--
--   $$\Big(\mathbb E\max_{i=1,\dots,k}\langle v_i,G\rangle\Big)^2\le C_k\sum_{i=1}^k\|v_i\|^2,$$
--
--   with equality when $v_i=z_i$ for all $i$, for some partition $\mathcal A\subseteq\mathbb R^{k-1}$ into $k$ sets with $F(\mathcal A)=C_k$.
--
--   This (Khot–Naor, Lemma 3.7) is used in Step 1 of Lemma 5.2.
--
--   **Formalization Note** The inequality is stated for every upper bound $C$ of $F$ over $k$-set partitions of every $\mathbb R^n$; $C_k$ is the least one. "$F(\mathcal A)=C_k$" is `AchievesCk`, and then $C_k=F(\mathcal A)$. The maximum is the reused `scoreMax`.
--
--   Differences from the source:
--   - encoding: C_k → any C with value B ≤ C for every k-cell IsPartition B of every Space n; reason: C_k is such a C, and the bound for C_k gives it for every larger C; no real sSup
--   - encoding: A achieves the supremum C_k (F(A) = C_k) → AchievesCk A: value A ≥ value B for every k-cell IsPartition B of every Space n; reason: a null modification changes no moment, so this is F(A) = C_k with C_k = value A; no real sSup is used
--   - generalization: A is a finite measurable partition of the space → IsPartition A: measurable cells, γ-almost every point in exactly one cell; reason: every exact partition is one, and the statement specializes to exact partitions
--   - encoding: indices i = 1, …, k → [NeZero k] for the finite maximum; reason: the paper's index set is nonempty
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), Lemma 2.3, p.5

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_HeilmanPropeller_AchievesCk

namespace HeilmanPropeller

open MeasureTheory OAI.GaussianPropeller
open OAI.GaussianPropeller.Reduction (scoreMax)
open scoped RealInnerProductSpace

/-- **Lemma 2.3 ([KN08, Lemma 3.7]).** Heilman, *On the Propeller Conjecture*, arXiv:2610.32158
(held version, sha256 13f5ddf8…), Lemma 2.3, p.5.

Let `G ∼ γ_{k−1}`. For any `v₁, …, v_k ∈ ℝ^{k−1}`,

  `(E maxᵢ ⟨vᵢ, G⟩)² ≤ C_k ∑ᵢ ‖vᵢ‖²`,

with equality when `vᵢ = zᵢ` for all `i`, for some partition `A ⊆ ℝ^{k−1}` with `F(A) = C_k`.

**Formalization Note.**
* `scoreMax v x = maxᵢ ⟪v i, x⟫` (reused; it needs `k ≥ 1`, the paper's index set `1, …, k` being
  nonempty). `E` is the integral against `gaussian (k − 1)`.
* Clause 1 is stated for every upper bound `C` of the values of `k`-cell partitions of every `ℝⁿ`.
  `C_k` is the least such bound and is one of them, so this is the same statement as with `C_k`,
  without a real `sSup`.
* Clause 2: "`F(A) = C_k`" is `AchievesCk A`, and then `C_k = value A`. -/
theorem lemma_2_3 (k : ℕ) [NeZero k] :
    (∀ C : ℝ, (∀ (n : ℕ) (B : Fin k → Set (Space n)), IsPartition B → value B ≤ C) →
      ∀ v : Fin k → Space (k - 1),
        (∫ x, scoreMax v x ∂(gaussian (k - 1))) ^ 2 ≤ C * ∑ i, ‖v i‖ ^ 2) ∧
    ∀ A : Fin k → Set (Space (k - 1)), AchievesCk A →
      (∫ x, scoreMax (fun i => centroid (A i)) x ∂(gaussian (k - 1))) ^ 2 =
        value A * ∑ i, ‖centroid (A i)‖ ^ 2 := by sorry

end HeilmanPropeller
