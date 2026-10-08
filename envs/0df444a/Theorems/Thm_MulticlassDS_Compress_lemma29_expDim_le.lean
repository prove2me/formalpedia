-- Prove2me | Theorems.Thm_MulticlassDS_Compress_lemma29_expDim_le
-- name    : MulticlassDS.Compress.lemma29_expDim_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:40:10.289576+00:00
-- url     : https://prove2.me/theorems/4b5c7a30-59b3-456a-8d16-ea2f91ed384e
-- title:
--   Lemma 29, p. 16 — d_E ≤ 5 d_N log p
-- statement:
--   For every $\mathcal H\subseteq[p]^n$ with Natarajan dimension $d_N = d_N(\mathcal H)$ and exponential dimension $d_E = d_E(\mathcal H)<\infty$,
--   $$d_E\ \le\ 5\,d_N\log p ,$$
--   with the logarithm in base $2$.
--
--   This relates the exponential dimension to the Natarajan dimension through the Haussler–Long generalization of Sauer's lemma, and with Corollary 28 gives Lemma 17.
--
--   **Formalization Note** Both dimensions are finite for $\mathcal H\subseteq[p]^n$ and are given as natural numbers. The logarithm is `Real.logb 2`. At $p\le1$ (where $\log p = 0$; Lean also sets $\log 0 = 0$) and at $d_N = 0$ the class has at most one element, so $d_E = 0$ and the statement holds as written; no hypothesis is added.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 16, Lemma 29

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Shifting

namespace MulticlassDS.Compress

theorem lemma29_expDim_le {n p : ℕ} (H : Set (Fin n → Fin p)) (dN dE : ℕ)
    (hN : natarajanDim H = dN) (hE : expDim H = dE) :
    (dE : ℝ) ≤ 5 * dN * Real.logb 2 p := by sorry

end MulticlassDS.Compress
