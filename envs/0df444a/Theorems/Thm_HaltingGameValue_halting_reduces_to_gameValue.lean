-- Prove2me | Theorems.Thm_HaltingGameValue_halting_reduces_to_gameValue
-- name    : HaltingGameValue.halting_reduces_to_gameValue
-- status  : Open
-- author  : @thomasvidick
-- created : 2026-10-15T08:29:53.289704+00:00
-- url     : https://prove2.me/theorems/7f0a0737-afba-4747-84f7-09fe6d0e0c6a
-- title:
--   Halting reduces to the synchronous game value (MIP* = RE, Theorem 12.2)
-- statement:
--   **Theorem 12.2 of "MIP\* = RE"** (Ji, Natarajan, Vidick, Wright, Yuen, arXiv:2001.04383), in synchronous form: the halting problem reduces to deciding whether the synchronous value of a nonlocal game is $1$ or at most $\tfrac12$.
--
--   Let $\mathcal{C}$ be the set of Turing machines, represented as Gödel numbers of partial recursive functions, and say that $c \in \mathcal{C}$ **halts on the empty input** when $c$ applied to the input $0$ is defined. A **game description** $g$ consists of two natural numbers $n_X, n_A$, a finite list of weighted question pairs $(x, y, w)$ and a finite list of accepted tuples $(x, y, a, b)$. It determines a synchronous game $G_g$ with question alphabet $X = \{0, \dots, n_X\}$ and answer alphabet $A = \{0, \dots, n_A\}$: the question distribution $\mu$ is the normalization of the listed weights (the point mass at $(0, 0)$ when the total listed weight is zero), and the decision predicate $D$ accepts exactly the listed tuples, except that unequal answers to equal questions are always rejected. The **synchronous value** $\omega_{\mathrm{s}}(G)$ of a synchronous game $G = (X, A, \mu, D)$ is the supremum, over all dimensions $d \ge 1$ and all families $(M^x_a)_{a \in A}$, $x \in X$, of projective measurements on $\mathbb{C}^d$, of the winning probability
--
--   $$
--   \omega(G, M) \;=\; \sum_{x, y \in X} \sum_{a, b \in A} \mu(x, y)\, D(x, y, a, b)\, \frac{\operatorname{Tr}\bigl(M^x_a M^y_b\bigr)}{d},
--   $$
--
--   in which both players measure the shared maximally entangled state of dimension $d$ with the same measurements.
--
--   The theorem asserts that there is a **computable** map $g : \mathcal{C} \to \{\text{game descriptions}\}$ such that for every machine $c$:
--
--   1. (**Completeness**) if $c$ halts on the empty input, then $\omega_{\mathrm{s}}(G_{g(c)}) = 1$;
--   2. (**Soundness**) if $c$ does not halt on the empty input, then $\omega_{\mathrm{s}}(G_{g(c)}) \le \tfrac12$.
--
--   Consequently no algorithm decides, given a game, whether its synchronous value is $1$ or at most $\tfrac12$. This is the headline statement of the formalization of $\mathrm{MIP}^* = \mathrm{RE}$; the paper's polynomial-time bound on $g$ and its version for the tensor-product value are strengthenings, both proved in the source repository.
--
--   **Formalization Note** The statement is the proposition `HaltingGameValue.HaltingReducesToGameValue` of the definition bundle `MIPRE_HaltingGameValue`, every definition of which is written over Mathlib alone. Machines are `Nat.Partrec.Code` and computability is Mathlib's `Computable`. A strategy is a question-indexed family of POVMs on $\mathbb{C}^d$ whose elements are idempotent, outcome probabilities are taken in the normalized trace $\operatorname{Tr}(\cdot)/d$ (the real part of the trace is used, so that the definition carries no proof obligation), and the supremum is Lean's `iSup` over all strategies in $\mathbb{R}$; the winning probabilities lie in $[0, 1]$. The proof, `HaltingGameValue.halting_reduces_to_gameValue` in `MIPRE/MainTheorem.lean` of https://github.com/vidick/MIPRE-formalization, depends on `propext`, `Classical.choice` and `Quot.sound` only.
-- source:
--   Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, MIP* = RE, arXiv:2001.04383 (2020, revised 2022), Theorem 12.2, in synchronous form and with polynomial time relaxed to computability. Lean statement: HaltingGameValue.HaltingReducesToGameValue in https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/HaltingGameValue.lean; Lean proof: HaltingGameValue.halting_reduces_to_gameValue in MIPRE/MainTheorem.lean of the same repository; blueprint node thm:main, https://vidick.github.io/MIPRE-formalization/blueprint/.

import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.PartrecCode
import Definitions.Def_MIPRE_HaltingGameValue

theorem HaltingGameValue.halting_reduces_to_gameValue : HaltingGameValue.HaltingReducesToGameValue := by sorry
