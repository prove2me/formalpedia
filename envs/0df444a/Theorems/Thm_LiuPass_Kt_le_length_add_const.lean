-- Prove2me | Theorems.Thm_LiuPass_Kt_le_length_add_const
-- name    : LiuPass.Kt_le_length_add_const
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T22:24:48.727621+00:00
-- url     : https://prove2.me/theorems/a9177634-6753-40c9-8e9a-3c494edbb964
-- title:
--   Fact 2.1: $K^t(x) \le |x| + c$
-- statement:
--   Fact 2.1 of the paper. For a fixed universal machine there is a constant $c$, depending only on
--   the machine, such that for **every** positive time bound $t$ and **every** string $x$,
--   $$K^{t}(x) \;\le\; |x| + c .$$
--
--   In words: a string is never much harder to describe than to write down. The witness is the
--   description that pairs the constant-size program "halt immediately, returning the input" with the
--   string $x$ itself, which runs in a single step and has length $|x| + c$.
--
--   The constant is uniform in $t$ and in $x$; in particular $c$ may not depend on the time bound.
--   Besides being used quantitatively in the construction of the one-way function from average-case
--   hardness (Theorem 4.1), this fact is what guarantees that the minimisation defining $K^t$ ranges
--   over a non-empty set.
-- source:
--   Yanyi Liu, Rafael Pass, On One-way Functions and Kolmogorov Complexity, arXiv:2009.11514v1 (FOCS 2020), https://arxiv.org/abs/2009.11514, p. 8, Fact 2.1

import Definitions.Def_LiuPass_crypto
open Finset
open scoped Classical

namespace LiuPass

open Finset
open scoped Classical

theorem Kt_le_length_add_const (U : UMachine) :
    ∃ c : ℕ, ∀ t : ℕ → ℕ, (∀ n, 0 < t n) → ∀ x : BitStr, Kt U t x ≤ x.length + c := by sorry
end LiuPass
