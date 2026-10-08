-- Prove2me | Theorems.Thm_MulticlassDS_Compress_claim22_shift_proj_card
-- name    : MulticlassDS.Compress.claim22_shift_proj_card
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:39:14.00063+00:00
-- url     : https://prove2.me/theorems/91a2f599-cb16-409e-8324-eb3e2d0dd6bd
-- title:
--   Claim 22, p. 14 — shifting does not increase projections: |S_i(H)|_S| ≤ |H|_S|
-- statement:
--   Let $\mathcal H\subseteq[p]^n$ and $i\in[n]$. For every sequence $S\in[n]^k$ of coordinates,
--   $$\big|\mathbb S_i(\mathcal H)|_S\big|\ \le\ \big|\mathcal H|_S\big| .$$
--
--   Together with its consequence Corollary 23, this lets the shifting argument control the exponential dimension.
--
--   **Formalization Note** A class $\mathcal H\subseteq[p]^n$ is viewed as a class of functions `Fin n → Fin p` on the domain `Fin n`, and $\mathcal H|_S$ is its projection to $S$; cardinalities are `Set.encard`. Labels are 0-based (see the `Shifting` definitions).
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 14, Claim 22

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Shifting

namespace MulticlassDS.Compress

theorem claim22_shift_proj_card {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) (k : ℕ)
    (S : Fin k → Fin n) :
    (proj (shift i H) S).encard ≤ (proj H S).encard := by sorry

end MulticlassDS.Compress
