-- Prove2me | Theorems.Thm_MulticlassDS_Compress_claim16_oig_one_correct
-- name    : MulticlassDS.Compress.claim16_oig_one_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:20:52.587834+00:00
-- url     : https://prove2.me/theorems/e868ffd8-6515-4cc4-8c4c-366c24f5de11
-- title:
--   Claim 16, p. 12 — on every realizable sample of size d+1 some leave-one-out prediction of the one-inclusion algorithm is correct
-- statement:
--   Let $\mathcal H\subseteq\mathcal Y^{\mathcal X}$ have DS dimension $d = d_{DS}(\mathcal H)<\infty$, and let $\mathcal A_{\mathcal H}$ be the one-inclusion algorithm (Algorithm 1). For every $\mathcal H$-realizable sample $S' = ((x'_1,y'_1),\dots,(x'_{d+1},y'_{d+1}))$ there is an index $i\in[d+1]$ with
--   $$h_{S'_{-i}}(x'_i) = y'_i,\qquad h_{S'_{-i}} = \mathcal A_{\mathcal H}(S'_{-i}),$$
--   where $S'_{-i}$ is $S'$ with its $i$-th example deleted.
--
--   This weak prediction guarantee is the starting point of the list learner (Proposition 32).
--
--   **Formalization Note** The one-inclusion algorithm is parametrized by a permutation-equivariant choice `C` of minimal orientations (see the `OneInclusion` definitions); the claim holds for every such choice. Equivariance makes the $d+1$ leave-one-out runs use one orientation of $\mathcal G(\mathcal H|_{(x'_1,\dots,x'_{d+1})})$, as the paper's proof requires. $S'_{-i}$ is `S' ∘ i.succAbove`. The label set is assumed non-empty, needed only to define the algorithm's default output on non-realizable inputs.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 12, Claim 16

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Compression
import Definitions.Def_MulticlassDS_Compress_OneInclusion

namespace MulticlassDS.Compress

theorem claim16_oig_one_correct {X Y : Type*} [Nonempty Y] (H : Set (X → Y)) (d : ℕ)
    (hd : dsDim H = d) (C : OIGChoice (projFamily H)) :
    ∀ S' : Fin (d + 1) → X × Y, IsRealizable H S' →
      ∃ i : Fin (d + 1), oigPredict C (S' ∘ i.succAbove) (S' i).1 = (S' i).2 := by sorry

end MulticlassDS.Compress
