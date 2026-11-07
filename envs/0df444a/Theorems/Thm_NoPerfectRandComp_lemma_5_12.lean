-- Prove2me | Theorems.Thm_NoPerfectRandComp_lemma_5_12
-- name    : NoPerfectRandComp.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:23.160534+00:00
-- url     : https://prove2.me/theorems/7e78b218-93b1-4d0a-a93a-dd07b97bcc3b
-- title:
--   Lemma 5.12 — matching outer upper bound $\mathrm{R}(W_q)=\Theta(su_q^2q^3)$
-- statement:
--   For $q = 2^s - 1$,
--   $$
--   \mathrm{R}(W_q) = \Theta(s\,u_q^2 q^3) :
--   $$
--   there are absolute constants $0 < c \le C$ and a threshold $s_0$ with $c\,s\,u_q^2q^3 \le \mathrm{R}(W_q) \le C\,s\,u_q^2 q^3$ for all $s \ge s_0$.
--
--   Together with (19) and the detector upper bound it identifies $\mathrm{R}(f)$ in Theorem 1.1.
--
--   Differences from the source:
--   - generalization: W_q with the paper's fixed encoding → every admissible encoding, with constants uniform in it; reason: the upper bound reads cells in full, the lower bound is Lemma 4.9, which holds for every admissible encoding
--   - encoding: Θ for q = 2^s − 1 ("for sufficiently large q" in the proof) → explicit constants and a threshold s₀; reason: definition of Θ
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 5.12, p.26

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_NoPerfectRandComp_W

namespace NoPerfectRandComp

/-- Lemma 5.12 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.26 (matching outer upper bound): `R(W_q) = Θ(s u_q² q³)` for
`q = 2ˢ − 1`.

**Formalization Note** `Θ` is explicit constants `0 < c ≤ C` and a threshold `s₀` (the proof's
"for sufficiently large q"), uniform in the encoding. -/
theorem lemma_5_12 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ s₀ : ℕ, ∀ s q : ℕ, s₀ ≤ s → q = 2 ^ s - 1 →
      ∀ enc : Encoding (aq q) (WCell q),
        c * s * (uq q : ℝ) ^ 2 * q ^ 3 ≤ Rt (W q enc) ∧
        (Rt (W q enc) : ℝ) ≤ C * s * (uq q : ℝ) ^ 2 * q ^ 3 := by sorry

end NoPerfectRandComp
