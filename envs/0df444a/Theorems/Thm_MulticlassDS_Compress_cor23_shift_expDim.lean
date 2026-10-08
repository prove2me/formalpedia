-- Prove2me | Theorems.Thm_MulticlassDS_Compress_cor23_shift_expDim
-- name    : MulticlassDS.Compress.cor23_shift_expDim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:39:44.019273+00:00
-- url     : https://prove2.me/theorems/6655bcc4-08e2-4aa8-a2cd-80eee128bace
-- title:
--   Corollary 23, p. 14 — shifting does not increase the exponential dimension
-- statement:
--   For every $\mathcal H\subseteq[p]^n$ and $i\in[n]$,
--   $$d_E\big(\mathbb S_i(\mathcal H)\big)\ \le\ d_E(\mathcal H).$$
--
--   Repeated shifting therefore reaches a downward-closed class without increasing the exponential dimension, which is the setting of Proposition 27.
--
--   **Formalization Note** $d_E$ takes values in `ℕ∞`; labels are 0-based (see the `Shifting` definitions).
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 14, Corollary 23

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Shifting

namespace MulticlassDS.Compress

theorem cor23_shift_expDim {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) :
    expDim (shift i H) ≤ expDim H := by sorry

end MulticlassDS.Compress
