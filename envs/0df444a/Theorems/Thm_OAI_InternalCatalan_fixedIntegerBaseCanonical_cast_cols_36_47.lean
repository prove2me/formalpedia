-- Prove2me | Theorems.Thm_OAI_InternalCatalan_fixedIntegerBaseCanonical_cast_cols_36_47
-- name    : OAI.InternalCatalan.fixedIntegerBaseCanonical_cast_cols_36_47
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:42.676187+00:00
-- url     : https://prove2.me/theorems/797a27a5-7447-491f-8f72-ddbc49fcec13
-- title:
--   OpenAI Catalan, §4.4 — columns 36–47 of the fixed matrix 𝓑 times D are the entries of OpenAI's integer table
-- statement:
--   Let $\mathcal B$ be the fixed rational $49\times48$ matrix of the paper's Eq. (47) (`fixedBaseEntryRat`), let $A$ be the explicit $49\times48$ integer matrix of the definitions bundle (`fixedIntegerBaseCanonical`, OpenAI's table: $A(r,k)=2\sum_{i<65}[t^i]P_r\,c_M(i,k)-3\sum_{i<65}[t^i]D_r\,c_Z(i,k)$ with the row polynomials $P_r,D_r$ at $N=1$ and two explicit integer tables $c_M,c_Z$ of cleared moments), and let
--
--   $$D=854041599922236190937524347070927377276592590715779683450880000.$$
--
--   For every row index $0\le r\le48$ and every column index $k$ with $36\le k\le 47$,
--
--   $$A(r,k)=D\cdot\mathcal B(r,k)\qquad\text{in }\mathbb Q.$$
--
--   So $D\mathcal B$ is an integer matrix, and the certificate of §4.4 may work with the integers $A(r,k)$: this is the clearing of denominators behind the reduction of $\mathcal B$ modulo $101$.
--
--   OpenAI, p. 24: “Every scalar denominator in these recipes is a product of nonzero integers of absolute value at most 65. Every rational array entry therefore has denominator prime factors at most 65, so each denominator is a unit modulo 101.”
--
--   **Formalization note.** The four column ranges ($0$–$11$, $12$–$23$, $24$–$35$, $36$–$47$) are not the paper's: OpenAI prove the identity for all columns at once (`fixedIntegerBaseCanonical_cast`), and it is split here only to keep each proof within the platform's size and time limits. The integer table $A$ is OpenAI's certificate data, not a construction of the paper. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 23-24, §4.4 (the fixed matrix B cleared of denominators), columns 36-47

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan


theorem fixedIntegerBaseCanonical_cast_cols_36_47 (r : Fin 49) (k : Fin 48)
    (hk : 36 ≤ k.val ∧ k.val < 48) :
    (fixedIntegerBaseCanonical r k : ℚ) = (854041599922236190937524347070927377276592590715779683450880000 : ℚ) * fixedBaseEntryRat r k := by
  sorry

end OAI.InternalCatalan
