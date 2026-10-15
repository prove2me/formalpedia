-- Prove2me | Theorems.Thm_MIPRE_Cost_mul_pow_le_two_pow
-- name    : MIPRE.Cost.mul_pow_le_two_pow
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:57.976479+00:00
-- url     : https://prove2.me/theorems/43e0ff5b-cc0a-456d-ad40-2cec742a7782
-- title:
--   Polynomial versus exponential growth: $A\sigma^D \le 2^{\sigma}$ once $\sigma \ge A(D+1)^{D+1}$
-- statement:
--   Let $A$, $D$ and $\sigma$ be natural numbers, and suppose that
--   $$ A \,(D+1)^{D+1} \le \sigma . $$
--   Then
--   $$ A\,\sigma^{D} \le 2^{\sigma} . $$
--
--   This is an explicit form of the fact that an exponential eventually dominates any monomial: for the monomial $A\sigma^D$, the point from which $2^\sigma$ dominates is at most $A(D+1)^{D+1}$. It is the arithmetic core of the threshold lemma `exists_threshold`, which in turn fixes the threshold $r(e) = 2^{K + 1 + |e|}$ of the recursive compression argument (blueprint `lem:recursive-compression`): above that threshold every polynomial overhead in $|e| + \log n$ is at most $n + 1$.
--
--   **Formalization Note**: All quantities are natural numbers and the inequality is stated with no side condition other than the displayed hypothesis; in particular $D = 0$ (where the hypothesis reads $A \le \sigma$ and the conclusion $A \le 2^\sigma$) and $A = 0$ are included. The proof is elementary (truncated division by $D+1$ and the bound $\mu + 1 \le 2^\mu$).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Growth.lean#L44-L66; internal lemma of the formalization of blueprint lem:recursive-compression, https://vidick.github.io/MIPRE-formalization/blueprint/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime

open MIPRE
open MIPRE.Cost
open Polynomial

theorem MIPRE.Cost.mul_pow_le_two_pow (A D σ : ℕ) (h : A * (D + 1) ^ (D + 1) ≤ σ) :
    A * σ ^ D ≤ 2 ^ σ := by sorry
