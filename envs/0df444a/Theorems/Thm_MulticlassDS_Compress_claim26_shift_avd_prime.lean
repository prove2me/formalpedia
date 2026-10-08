-- Prove2me | Theorems.Thm_MulticlassDS_Compress_claim26_shift_avd_prime
-- name    : MulticlassDS.Compress.claim26_shift_avd_prime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:39:29.309134+00:00
-- url     : https://prove2.me/theorems/5a943c11-c199-4f2d-b0fb-2d0ba42c304a
-- title:
--   Claim 26, p. 15 — shifting does not decrease avd′
-- statement:
--   For every $\mathcal H\subseteq[p]^n$ and $i\in[n]$,
--   $$\operatorname{avd}'\big(\mathbb S_i(\mathcal H)\big)\ \ge\ \operatorname{avd}'(\mathcal H).$$
--
--   Unlike the average degree, which can drop under multiclass shifting (Example 20), $\operatorname{avd}'$ is monotone, which makes it the quantity tracked in the proof of Proposition 27.
--
--   **Formalization Note** $\operatorname{avd}'$ is the real number of Definition 25 (see the `Shifting` definitions); labels are 0-based. The page prints a stray closing parenthesis, "avd′(S_i(H)))"; it has no meaning.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 15, Claim 26

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Shifting

namespace MulticlassDS.Compress

theorem claim26_shift_avd_prime {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) :
    avd' H ≤ avd' (shift i H) := by sorry

end MulticlassDS.Compress
