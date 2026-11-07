-- Prove2me | Theorems.Thm_NoPerfectRandComp_eq_29
-- name    : NoPerfectRandComp.eq_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:29.222111+00:00
-- url     : https://prove2.me/theorems/576937fc-5d75-43e8-9603-5119a1e3ee83
-- title:
--   Eq. (29) — $\mathrm{R}(W_q\circ\hat M_q)\le 9c_qu_q^2B_q+(36a_q+c_qu_q^2)q^3\hat C_q$, hence (20)
-- statement:
--   For $q = 2^s - 1$ and all sufficiently large $s$,
--   $$
--   \mathrm{R}(W_q \circ \hat M_q) \ \le\ 9 c_q u_q^2 B_q + (36 a_q + c_q u_q^2)\, q^3 \hat C_q ,
--   $$
--   and consequently, with an absolute constant $K$,
--   $$
--   \mathrm{R}(W_q \circ \hat M_q) \ \le\ K\, s\, u_q^2 q^5 b_q . \tag{20}
--   $$
--   Composition places an independent copy of $\hat M_q$ at every Boolean coordinate of $W_q$. This is the upper half of Theorem 5.1.
--
--   Differences from the source:
--   - generalization: the paper's fixed encodings of W_q and M̂_q → every pair of admissible encodings; reason: the algorithm runs Lemmas 5.10, 5.11 and reads outer bits by evaluating inner blocks in full
--   - encoding: "for sufficiently large q" and the O of (20) → a threshold s₀ and an explicit constant K; reason: definition
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Eq. (29), p.26; Eq. (20), p.18

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_W
import Definitions.Def_NoPerfectRandComp_Mhat
import Definitions.Def_NoPerfectRandComp_Bq__ccb8cb

namespace NoPerfectRandComp

/-- Inequality (29) of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.26, and its consequence (20), p.18: for `q = 2ˢ − 1` and all
sufficiently large `s`,
`R(W_q ∘ M̂_q) ≤ 9 c_q u_q² B_q + (36 a_q + c_q u_q²) q³ Ĉ_q`, which is `O(s u_q² q⁵ b_q)`.

**Formalization Note** Composition places an independent copy of `M̂_q` at every Boolean
coordinate of `W_q`. "Sufficiently large" is a threshold `s₀`; the `O` of (20) is an explicit
constant `K`. Stated for every pair of admissible encodings. -/
theorem eq_29 :
    (∃ s₀ : ℕ, ∀ s q : ℕ, s₀ ≤ s → q = 2 ^ s - 1 →
      ∀ (encW : Encoding (aq q) (WCell q)) (encM : Encoding (bq q) (PtrCell q)),
        Rt (OAI.Paper320.compose (W q encW) (Mhat q encM)) ≤
          9 * cq q * uq q ^ 2 * Bq q + (36 * aq q + cq q * uq q ^ 2) * q ^ 3 * Chat q) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ s₀ : ℕ, ∀ s q : ℕ, s₀ ≤ s → q = 2 ^ s - 1 →
      ∀ (encW : Encoding (aq q) (WCell q)) (encM : Encoding (bq q) (PtrCell q)),
        (Rt (OAI.Paper320.compose (W q encW) (Mhat q encM)) : ℝ) ≤
          K * s * (uq q : ℝ) ^ 2 * q ^ 5 * bq q) := by sorry

end NoPerfectRandComp
