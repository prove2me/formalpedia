-- Prove2me | Theorems.Thm_MIPRE_Cost_exists_threshold
-- name    : MIPRE.Cost.exists_threshold
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:58.842027+00:00
-- url     : https://prove2.me/theorems/439ce6b2-b6c0-4d7d-aea2-6109d6e0e6aa
-- title:
--   The threshold lemma: a polynomial in $x + \log n$ is at most $n+1$ once $n \ge 2^{K+1+x}$
-- statement:
--   Let $Q \in \mathbb{N}[X]$ be a polynomial with natural-number coefficients. For $n \in \mathbb{N}$ write $\log n$ for the binary length of $n$, that is, the number of binary digits of $n$ ($\log 0 = 0$ and $\log n = \lfloor \log_2 n \rfloor + 1$ for $n \ge 1$; in Lean, `Nat.size n`). Then there is a constant $K \in \mathbb{N}$ such that for all $x, n \in \mathbb{N}$,
--   $$ 2^{K + 1 + x} \le n \;\Longrightarrow\; Q(x + \log n) \le n + 1 . $$
--
--   The constant depends on $Q$ only. The lemma is the quantitative input of the recursive compression argument (blueprint `lem:recursive-compression`, [MNY, Lemma 5.1]): the compression map has polynomial overhead $Q(|e| + \log n)$ in the size of the description $e$ and the binary length of the index $n$, and the threshold $r(e) = 2^{K + 1 + |e|}$ is chosen so that above it this overhead is at most $n + 1$, which is what lets the compressed description be shorter than the string it describes.
--
--   **Formalization Note**: $Q$ is a `Polynomial ℕ` evaluated with `Polynomial.eval`, so it is monotone; the logarithm is `Nat.size`. The proof produces the explicit constant $K = 2A\,2^D (D+1)^{D+1}$ where $D$ is the degree of $Q$ and $A$ the sum of its coefficients, and in fact bounds $Q(x + \log n)$ by $n$; the statement keeps the slack $n + 1$. The hypothesis is $2^{K+1+x} \le n$, with the exponent $K + 1 + x$ as written.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Growth.lean#L68-L98; internal lemma of the formalization of blueprint lem:recursive-compression, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Cost.exists_threshold (Q : Polynomial ℕ) :
    ∃ K : ℕ, ∀ x n : ℕ, 2 ^ (K + 1 + x) ≤ n → Q.eval (x + Nat.size n) ≤ n + 1 := by sorry
