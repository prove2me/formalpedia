-- Prove2me | Theorems.Thm_MulticlassDS_Compress_prop27_avd_le_four_expDim
-- name    : MulticlassDS.Compress.prop27_avd_le_four_expDim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:39:45.762979+00:00
-- url     : https://prove2.me/theorems/9a9031c8-661e-469a-adc6-6606a951b598
-- title:
--   Proposition 27, p. 15 — avd(H) ≤ 4 d_E(H)
-- statement:
--   For every $\mathcal H\subseteq[p]^n$,
--   $$\operatorname{avd}(\mathcal H)\ \le\ 4\,d_E(\mathcal H).$$
--
--   Since every subclass also satisfies the bound, the one-inclusion graph always has a vertex of degree at most $4d_E(\mathcal H)$, which gives orientations of small out-degree (Corollary 28).
--
--   **Formalization Note** The exponential dimension is finite for $\mathcal H\subseteq[p]^n$ (since $|\mathcal H|_S|\le p^n$), so it is given as a natural number $d_E$ with `expDim H = dE`. For the empty class the average degree is $0$. Labels are 0-based.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 15, Proposition 27

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Shifting

namespace MulticlassDS.Compress

theorem prop27_avd_le_four_expDim {n p : ℕ} (H : Set (Fin n → Fin p)) (dE : ℕ)
    (hE : expDim H = dE) :
    avd H ≤ 4 * dE := by sorry

end MulticlassDS.Compress
