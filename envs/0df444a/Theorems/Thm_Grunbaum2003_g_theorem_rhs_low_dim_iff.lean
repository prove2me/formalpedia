-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_rhs_low_dim_iff
-- name    : Grunbaum2003.g_theorem_rhs_low_dim_iff
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:21.038326+00:00
-- url     : https://prove2.me/theorems/77ffd84e-1a0d-4d1c-b1df-bf1c9921fbf2
-- title:
--   Low-dimensional $M$-sequence and $g$-matrix characterizations ($d = 1, 2, 3$)
-- statement:
--   This theorem characterizes the arithmetic right-hand side of the Billera–Lee–Stanley $g$-theorem (`IsMSequence (d / 2) g` and the linear transformation `gTheoremMatrix d`) in low dimensions $d \in \{1, 2, 3\}$.
--
--   1. **Length-one Macaulay condition ($\lfloor d/2 \rfloor = 1$):** A sequence $g : \mathbb{N} \to \mathbb{N}$ satisfies `IsMSequence 1 g` if and only if $g_0 = 1$ (since $g_1 = \binom{g_1}{1}$ has upper pseudopower $\binom{g_1 - 1}{0} = 1 = g_0$ whenever $g_1 > 0$).
--   2. **Dimension $d = 1$ ($\lfloor 1/2 \rfloor = 0$):** For $f : \operatorname{Fin} 2 \to \mathbb{Z}$, the $g$-theorem sum holds for some $M$-sequence $g$ of length $1$ if and only if $f(0) = 1$ and $f(1) = 2$.
--   3. **Dimension $d = 2$ ($\lfloor 2/2 \rfloor = 1$):** For $f : \operatorname{Fin} 3 \to \mathbb{Z}$, the $g$-theorem sum holds if and only if $f(0) = 1$ and there exists $n \in \mathbb{N}$ ($n = g_1$) such that $f(1) = n + 3$ and $f(2) = n + 3$.
--   4. **Dimension $d = 3$ ($\lfloor 3/2 \rfloor = 1$):** For $f : \operatorname{Fin} 4 \to \mathbb{Z}$, the $g$-theorem sum holds if and only if $f(0) = 1$ and there exists $n \in \mathbb{N}$ ($n = g_1$) such that
--      $$
--      f(1) = n + 4, \qquad f(2) = 3n + 6, \qquad f(3) = 2n + 4,
--      $$
--      recovering Steinitz's characterization of $f$-vectors of simplicial $3$-polytopes.
--
--   **Formalization Note** Expanding `Finset.range (d / 2 + 1)` and `gTheoremMatrix d j k` reduces each low-dimensional equivalence to explicit binomial evaluations and Presburger arithmetic.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §10.6, pp. 198a–198b

import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem g_theorem_rhs_low_dim_iff :
    (∀ g : ℕ → ℕ, IsMSequence 1 g ↔ g 0 = 1) ∧
    (∀ f : Fin 2 → ℤ,
      (∃ g : ℕ → ℕ, IsMSequence (1 / 2) g ∧
        ∀ k : Fin 2, f k = ∑ j ∈ Finset.range (1 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 1 j k.val) ↔
        f 0 = 1 ∧ f 1 = 2) ∧
    (∀ f : Fin 3 → ℤ,
      (∃ g : ℕ → ℕ, IsMSequence (2 / 2) g ∧
        ∀ k : Fin 3, f k = ∑ j ∈ Finset.range (2 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 2 j k.val) ↔
        f 0 = 1 ∧ ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3) ∧
    (∀ f : Fin 4 → ℤ,
      (∃ g : ℕ → ℕ, IsMSequence (3 / 2) g ∧
        ∀ k : Fin 4, f k = ∑ j ∈ Finset.range (3 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 3 j k.val) ↔
        f 0 = 1 ∧ ∃ n : ℕ,
          f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4) := by sorry

end Grunbaum2003
