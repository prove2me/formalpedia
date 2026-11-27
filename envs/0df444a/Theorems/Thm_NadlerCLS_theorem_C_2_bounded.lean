-- Prove2me | Theorems.Thm_NadlerCLS_theorem_C_2_bounded
-- name    : NadlerCLS.theorem_C_2_bounded
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-26T23:28:40.834954+00:00
-- url     : https://prove2.me/theorems/8adeab64-f977-500a-87cd-b19ed8614dc8
-- title:
--   Theorem C.2 with polynomially short decoded answers
-- statement:
--   Theorem C.2 with short decoded answers.
--
--   Fix $n\ge1$ and a rational $\beta\in(0,1]$. There is a natural number $k$ and a polynomial-time search reduction from $\beta$-Hölder-LocalOpt on $[0,1]^n$, with answers restricted to length at most $(|s|+1)^k+k$ in the instance length $|s|$, to Continuous-LocalOpt on $[0,1]^n$ (Definition 2, $\ell_1$ norm).
--
--   Explicitly: there are polynomial-time maps $F$ (instances) and $G$ (answers) such that for every valid instance $s$ of $\beta$-Hölder-LocalOpt, $F(s)$ is a valid instance of Continuous-LocalOpt, and for **every** answer $t$ of $F(s)$, of any length, $G(s\#t)$ is an answer of $s$ of length at most $(|s|+1)^k+k$.
--
--   This is the reduction of Theorem C.2, in which the decoder must in addition return polynomially short answers even when it is handed a long answer of the target instance. It is what CLS-membership of $\beta$-Hölder-LocalOpt needs once membership in TFNP requires polynomially bounded answers (Theorem C.4).
--
--   **Formalization Note** The source problem is the public `bounded (holderSearch n β) k`, the target `coSearch n`, and reductions are the public `SearchReduces` (Cook's one-tape machines). Since answers of the bounded problem are answers of the unbounded one, this statement implies `NadlerCLS.theorem_C_2`.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101v4, Theorem C.2, p.34, with its proof pp.34–36 (interpolated instance, conditions (C.4), comparisons 1–4, (C.5)), and Lemma C.6, p.38 ("respects the polynomial witness size"); used for Theorem C.4, p.37.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_coSearch
import Definitions.Def_NadlerCLS_holderSearch

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

theorem theorem_C_2_bounded (n : ℕ) (hn : 1 ≤ n) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∃ k : ℕ, SearchReduces (bounded (holderSearch n β) k) (coSearch n) := by sorry

end NadlerCLS
