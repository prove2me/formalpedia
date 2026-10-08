-- Prove2me | Theorems.Thm_MulticlassDS_Compress_lemma17_orientation_natarajan
-- name    : MulticlassDS.Compress.lemma17_orientation_natarajan
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:21:11.285311+00:00
-- url     : https://prove2.me/theorems/8ac5fdb7-3779-4bf0-9081-8a43ac48e70f
-- title:
--   Lemma 17, p. 12 — H ⊆ [p]^n has an orientation of maximum out-degree ≤ 20 d_N log p
-- statement:
--   Let $\mathcal H\subseteq[p]^n$ have Natarajan dimension $d_N<\infty$. Then the one-inclusion graph $\mathcal G(\mathcal H)$ has an orientation $\sigma$ with maximum out-degree
--   $$\operatorname{outdeg}(\sigma)\ \le\ 20\,d_N\log p ,$$
--   with the logarithm in base $2$.
--
--   This is the main result of §3; through Proposition 34 it controls the error of the one-inclusion learner given a menu of size $p$.
--
--   **Formalization Note** The maximum out-degree bound is a bound on every vertex's out-degree; the logarithm is `Real.logb 2`. At $p\le1$ the bound is $0$, which holds because $\mathcal H$ has at most one word and every edge is a singleton.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 12, Lemma 17 (and Remark, p. 16)

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_OneInclusion

namespace MulticlassDS.Compress

theorem lemma17_orientation_natarajan {n p : ℕ} (H : Set (Fin n → Fin p)) (dN : ℕ)
    (hN : natarajanDim H = dN) :
    ∃ σ : Orientation H, ∀ v ∈ H, (outdeg σ v : ℝ) ≤ 20 * dN * Real.logb 2 p := by sorry

end MulticlassDS.Compress
