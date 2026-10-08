-- Prove2me | Theorems.Thm_MulticlassDS_Compress_lemma13_orientation_le_d
-- name    : MulticlassDS.Compress.lemma13_orientation_le_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:20:43.951668+00:00
-- url     : https://prove2.me/theorems/bdbf46f6-7156-42a6-87d7-c57ce86e8f65
-- title:
--   Lemma 13, p. 9 — H ⊆ Y^{d+1} of DS dimension ≤ d has an orientation of maximum out-degree ≤ d
-- statement:
--   Let $d\in\mathbb N$ and let $\mathcal H\subseteq\mathcal Y^{d+1}$ be a class of words of length $d+1$, possibly infinite, with DS dimension $d_{DS}(\mathcal H)\le d$. Then the one-inclusion graph $\mathcal G(\mathcal H)$ has an orientation $\sigma$ with
--   $$\operatorname{outdeg}(\sigma)\ \le\ d .$$
--
--   Since $\mathcal H$ has $d+1$ directions, this says that every vertex has at least one incoming edge. It is the combinatorial core of the one-inclusion learner: it turns a DS dimension bound into a prediction guarantee (Claim 16).
--
--   **Formalization Note** The page assumes "DS dimension $d$"; the statement here assumes $d_{DS}(\mathcal H)\le d$, which is equivalent: applying the page's statement at the actual dimension $d'\le d$ gives out-degree $\le d'\le d$ (and a class in $\mathcal Y^{d+1}$ has DS dimension $\le d+1$, with $d+1$ excluded by the hypothesis). The maximum out-degree bound is written as a bound on every vertex's out-degree. Orientations are encoded as in the `OneInclusion` definitions.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 9, Lemma 13 (infinite case: Appendix B, pp. 34–35)

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_OneInclusion

namespace MulticlassDS.Compress

theorem lemma13_orientation_le_d {Y : Type*} (d : ℕ) (H : Set (Fin (d + 1) → Y))
    (hH : dsDim H ≤ d) :
    ∃ σ : Orientation H, ∀ v ∈ H, outdeg σ v ≤ d := by sorry

end MulticlassDS.Compress
