-- Prove2me | Theorems.Thm_MTT_Eigenform_epsilon_neg_one_eq_neg_one_pow
-- name    : MTT.Eigenform.epsilon_neg_one_eq_neg_one_pow
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-26T20:50:13.946985+00:00
-- url     : https://prove2.me/theorems/2236fdd9-912a-4123-a6ab-17dea352a576
-- title:
--   The nebentype of a normalized eigenform has the parity of its weight
-- statement:
--   Let $f$ be a normalized algebraic cuspidal eigenform of level $N$ and nonnegative integral weight $k$, with nebentype $\varepsilon$ and a fixed complex embedding of its coefficients. Then
--
--   $$\varepsilon(-1)=(-1)^k.$$
--
--   In particular, the nebentype is even when the weight is even, and odd when the weight is odd. The even-weight case supplies the parity input for choosing an admissible quadratic seed in the mission's minimal-level Friedberg–Hoffstein reduction.
--
--   **Formalization Note.** The equality is in the algebraic closure of the rationals. The statement uses the mission's normalized eigenform structure and does not require a newform or positive-level hypothesis. Its formal boundary cases $N=0$ and $k=0$ follow from the same transformation law.
-- source:
--   William Stein, Modular Forms: A Computational Approach, Chapter 6, section 'Modular Forms with Character', opening paragraph (the parity compatibility condition), https://wstein.org/books/modform/modform/dimension_formulas.html#modular-forms-with-character. The proof is the elementary specialization of the nebentype transformation law to -I; normalization supplies nonzeroness. The cited section considers positive levels and weights at least two; the same calculation also proves the formal boundary cases in this statement.

import Definitions.Def_MTT_Arithmetic

set_option autoImplicit false

theorem MTT.Eigenform.epsilon_neg_one_eq_neg_one_pow {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (f : MTT.Eigenform N k ι) : f.epsilon (-1) = (-1) ^ k := by sorry
