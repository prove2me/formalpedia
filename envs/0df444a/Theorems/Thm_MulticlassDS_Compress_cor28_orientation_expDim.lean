-- Prove2me | Theorems.Thm_MulticlassDS_Compress_cor28_orientation_expDim
-- name    : MulticlassDS.Compress.cor28_orientation_expDim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:39:54.154687+00:00
-- url     : https://prove2.me/theorems/e2b67ee3-cdb8-457f-a125-e099579f5626
-- title:
--   Corollary 28, p. 16 — G(H) has an orientation of maximum out-degree ≤ 4 d_E(H)
-- statement:
--   For every $\mathcal H\subseteq[p]^n$ there is an orientation $\sigma$ of the one-inclusion graph $\mathcal G(\mathcal H)$ with maximum out-degree
--   $$\operatorname{outdeg}(\sigma)\ \le\ 4\,d_E(\mathcal H).$$
--
--   Combined with Lemma 29 this gives Lemma 17.
--
--   **Formalization Note** $d_E(\mathcal H)$ is finite and given as a natural number $d_E$ with `expDim H = dE`; the maximum out-degree bound is a bound on every vertex's out-degree. Orientations are encoded as in the `OneInclusion` definitions.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 16, Corollary 28

import Mathlib
import Definitions.Def_MulticlassDS_Compress_OneInclusion
import Definitions.Def_MulticlassDS_Compress_Shifting

namespace MulticlassDS.Compress

theorem cor28_orientation_expDim {n p : ℕ} (H : Set (Fin n → Fin p)) (dE : ℕ)
    (hE : expDim H = dE) :
    ∃ σ : Orientation H, ∀ v ∈ H, outdeg σ v ≤ 4 * dE := by sorry

end MulticlassDS.Compress
