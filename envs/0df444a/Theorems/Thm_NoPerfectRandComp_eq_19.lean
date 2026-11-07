-- Prove2me | Theorems.Thm_NoPerfectRandComp_eq_19
-- name    : NoPerfectRandComp.eq_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:40.180013+00:00
-- url     : https://prove2.me/theorems/ccc2c680-8508-4fed-8edb-b3c30584a261
-- title:
--   Eq. (19) — $\mathrm{R}(\hat M_q)\ge(T+1)(12b_q+1)\ge b_qq^2s/10^6$
-- statement:
--   Let $q = 2^s - 1$ with $s \ge 1000$ and $T = \lfloor q^2 s/10^6\rfloor$. Then
--   $$
--   \mathrm{R}(\hat M_q) \ \ge\ (T+1)(12b_q + 1) \ \ge\ \frac{b_q q^2 s}{10^6} .
--   $$
--   This is the inner lower bound of Theorem 5.1, obtained from Lemma 5.8 through the transfer Lemma 5.9.
--
--   **Formalization Note** Both inequalities of the chain are stated, for every admissible encoding.
--
--   Differences from the source:
--   - generalization: M̂_q with the paper's fixed pointer-cell encoding → every admissible encoding; reason: the transfer Lemma 5.9 uses only the privacy of Lemma 4.5 and fixed representatives, which a surjective decoder provides
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Eq. (19), pp.18 and 24 (via Lemmas 5.8 and 5.9)

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_Mhat

namespace NoPerfectRandComp

/-- Inequality (19) of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.24 (via Lemmas 5.8 and 5.9): for `q = 2ˢ − 1` and `s ≥ 1000`,
`R(M̂_q) ≥ (T + 1)(12 b_q + 1) ≥ b_q q² s / 10⁶` with `T = ⌊q² s / 10⁶⌋`.

**Formalization Note** Both inequalities of the displayed chain are stated, for every admissible
encoding. -/
theorem eq_19 (s q : ℕ) (hs : 1000 ≤ s) (hq : q = 2 ^ s - 1) (enc : Encoding (bq q) (PtrCell q)) :
    (q ^ 2 * s / 10 ^ 6 + 1) * (12 * bq q + 1) ≤ Rt (Mhat q enc) ∧
    (bq q : ℝ) * q ^ 2 * s / 10 ^ 6 ≤ Rt (Mhat q enc) := by sorry

end NoPerfectRandComp
