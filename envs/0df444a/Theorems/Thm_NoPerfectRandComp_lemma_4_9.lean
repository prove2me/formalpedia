-- Prove2me | Theorems.Thm_NoPerfectRandComp_lemma_4_9
-- name    : NoPerfectRandComp.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:50.592921+00:00
-- url     : https://prove2.me/theorems/e095dac6-5402-4e67-8d2a-98f1292d7ebc
-- title:
--   Lemma 4.9 — ordinary-query lower bound $\mathrm{R}(W_q)>25\ell_qu_q^2q^3$
-- statement:
--   For $q \ge 4$, with $\ell_q = \lceil\log_2 q\rceil$,
--   $$
--   \mathrm{R}(W_q) \ >\ 25\,\ell_q\, u_q^2 q^3 .
--   $$
--   This is the outer lower bound (18) of Theorem 5.1.
--
--   **Formalization Note** The bound is stated for $W_q$ built from every admissible private cell encoding.
--
--   Differences from the source:
--   - generalization: W_q with the paper's fixed (lexicographically first) encoding → W_q for every admissible encoding (private linear map and surjective decoder); reason: the proof uses only the privacy of Lemma 4.5 and the surjectivity of the decoder, and the paper's encoding is admissible
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 4.9, p.16; Eq. (18), p.18

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_W

namespace NoPerfectRandComp

/-- Lemma 4.9 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.16 (ordinary-query lower bound): for `q ≥ 4`,
`R(W_q) > 25 ℓ_q u_q² q³` with `ℓ_q = ⌈log₂ q⌉`. This is (18), p.18.

**Formalization Note** Stated for every admissible cell encoding `enc` (the paper fixes one).
`⌈log₂ q⌉` is `Nat.clog 2 q`. -/
theorem lemma_4_9 (q : ℕ) (hq : 4 ≤ q) (enc : Encoding (aq q) (WCell q)) :
    25 * Nat.clog 2 q * uq q ^ 2 * q ^ 3 < Rt (W q enc) := by sorry

end NoPerfectRandComp
