-- Prove2me | Theorems.Thm_MulticlassDS_Compress_lemma39_list_compression
-- name    : MulticlassDS.Compress.lemma39_list_compression
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:03:56.928635+00:00
-- url     : https://prove2.me/theorems/d5aa0ae0-af8f-4881-883a-c47cffff2658
-- title:
--   Lemma 39, p. 23 — an n → r₁ list sample compression scheme with r₁ ≤ (d+t+1)/(t+1)·(d+t) log 2n and menu size ≤ C(d+t+1, t+1) log 2n
-- statement:
--   Let $\mathcal H\subseteq\mathcal Y^{\mathcal X}$ have DS dimension $d_{DS}<\infty$. For all integers $n,t>0$ there is an $n\to r_1$ list sample compression scheme for $\mathcal H$ with menu size $p$, where
--   $$r_1\ \le\ \frac{d_{DS}+t+1}{t+1}\,(d_{DS}+t)\log(2n)\qquad\text{and}\qquad p\ \le\ \binom{d_{DS}+t+1}{t+1}\log(2n).$$
--   Logarithms are base $2$.
--
--   This is the first component of the compression scheme of Theorem 36: a short subsample from which a small menu of candidate labels for every point is reconstructed.
--
--   **Formalization Note** The scheme is asserted to exist; no learner appears in the statement. Logarithms are `Real.logb 2`, and $\log(2n)\ge1$ for $n\ge1$. The bound $(d_{DS}+t+1)/(t+1)$ is a fraction and $\binom{d_{DS}+t+1}{t+1}$ a binomial coefficient, as on the page.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 23, Lemma 39

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Compression

namespace MulticlassDS.Compress

theorem lemma39_list_compression {X Y : Type*} (H : Set (X → Y)) (d : ℕ) (hd : dsDim H = d)
    (n t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    ∃ r₁ p : ℕ,
      (r₁ : ℝ) ≤ ((d : ℝ) + t + 1) / (t + 1) * (d + t) * Real.logb 2 (2 * (n : ℝ)) ∧
      (p : ℝ) ≤ (Nat.choose (d + t + 1) (t + 1) : ℝ) * Real.logb 2 (2 * (n : ℝ)) ∧
      ∃ ρ : (Fin r₁ → X × Y) → X → Set Y, IsListCompressionScheme H n r₁ p ρ := by sorry

end MulticlassDS.Compress
