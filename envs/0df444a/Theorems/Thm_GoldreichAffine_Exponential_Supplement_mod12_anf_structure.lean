-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_Supplement_mod12_anf_structure
-- name    : GoldreichAffine.Exponential.Supplement.mod12_anf_structure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:51:33.286185+00:00
-- url     : https://prove2.me/theorems/d905d21c-e945-4056-9b38-4fb8ae5285c4
-- title:
--   Lemma 8 — structure of the ANF coefficients of MOD12
-- statement:
--   Let $\lambda_j(w)=\sum_{h=0}^{j}\binom jh a(w+h)\in\mathbb F_2$ with $a(h)=1$ if $h\bmod12\notin\{0,1,3,4,6,9\}$ and $a(h)=0$ otherwise; these are the ANF coefficients of $\mathsf{MOD12}_b$. For every $w\ge0$ and every $j\ge4$,
--
--   $$\lambda_{j+12}(w)=\lambda_j(w),\qquad\lambda_j(w+4)=\lambda_{j+8}(w).$$
--
--   Moreover, for every $w\ge0$:
--
--   1. the sequence $(\lambda_j(w))_{j\ge4}$ contains no six consecutive zeros, i.e. for every $j\ge4$ some $i$ with $j\le i\le j+5$ has $\lambda_i(w)\ne0$;
--   2. at least one of $\lambda_4(w),\lambda_5(w),\lambda_6(w)$ is nonzero.
--
--   The degree lower bound of Theorem 4 is read off these clauses.
--
--   Differences from the source:
--   - encoding: (λ_j(w))_{j≥4} contains no six consecutive zeros → ∀ w, ∀ j ≥ 4, ∃ i, j ≤ i ≤ j+5 ∧ λ_i(w) ≠ 0; reason: same statement, quantified explicitly
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, p. 31 (PDF p. 32), Lemma 8; proof pp. 31–32 (PDF pp. 32–33)

import Definitions.Def_GoldreichAffine_Exponential_Supplement_Modular
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- Lemma 8, printed p.31 / PDF p.32: all four clauses, for every w ≥ 0. -/
theorem mod12_anf_structure :
    (∀ w j : ℕ, 4 ≤ j →
      binomialTransform mod12Sequence (j + 12) w = binomialTransform mod12Sequence j w ∧
      binomialTransform mod12Sequence j (w + 4) = binomialTransform mod12Sequence (j + 8) w) ∧
    (∀ w j : ℕ, 4 ≤ j → ∃ i : ℕ, j ≤ i ∧ i ≤ j + 5 ∧ binomialTransform mod12Sequence i w ≠ 0) ∧
    (∀ w : ℕ, binomialTransform mod12Sequence 4 w ≠ 0 ∨
      binomialTransform mod12Sequence 5 w ≠ 0 ∨ binomialTransform mod12Sequence 6 w ≠ 0) := by sorry

end GoldreichAffine.Exponential.Supplement
