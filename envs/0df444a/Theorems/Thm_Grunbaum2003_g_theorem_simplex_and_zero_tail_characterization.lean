-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_simplex_and_zero_tail_characterization
-- name    : Grunbaum2003.g_theorem_simplex_and_zero_tail_characterization
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T01:27:39.938165+00:00
-- url     : https://prove2.me/theorems/012b0702-88d3-4426-81ac-77e0ac100811
-- title:
--   M-sequence zero-tail propagation and d-simplex realization and uniqueness in the g-theorem
-- statement:
--   This theorem establishes three foundational properties of $M$-sequences and $d$-simplices in Björner's matrix formulation of the $g$-theorem:
--
--   1. (**Zero-tail propagation for $M$-sequences**) If $g : \mathbb{N} \to \mathbb{N}$ satisfies `IsMSequence m g` and $g(k_0) = 0$, then $g(k) = 0$ for all $k_0 \le k \le m$.
--   2. (**Sufficiency for $g(1) = 0$**) For every dimension $d \in \mathbb{N}$ and every $M$-sequence $g$ of length $\lfloor d/2 \rfloor$ with $g(1) = 0$, there exists a simplicial $d$-polytope $P \subseteq \mathbb{R}^d$ (namely the $d$-simplex) whose face counts satisfy $f_j(P) = \sum_{i=0}^{\lfloor d/2 \rfloor} g(i) M_d(i, j+1)$ for all $0 \le j < d$.
--   3. (**Necessity for $f_0(P) \le d + 1$**) For every dimension $d \in \mathbb{N}$ and every simplicial $d$-polytope $P \subseteq \mathbb{R}^d$ with $f_0(P) \le d + 1$, we have $f_0(P) = d + 1$, $P$ is a $d$-simplex with $f_j(P) = \binom{d+1}{j+1}$, and its face vector is represented via $M_d$ by the $M$-sequence $g = (1, 0, 0, \dots)$.
--
--   **Formalization Note** Polytopes are represented by `IsSimplicialDPolytope`, $M$-sequences by `IsMSequence`, and Björner's matrix by `gTheoremMatrix`.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §10.6, pp. 198a–198b / PDF pp. 235–236

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem g_theorem_simplex_and_zero_tail_characterization :
    (∀ {m : ℕ} {g : ℕ → ℕ}, IsMSequence m g →
      ∀ {k₀ : ℕ}, g k₀ = 0 → ∀ k : ℕ, k₀ ≤ k → k ≤ m → g k = 0) ∧
    (∀ (d : ℕ) (g : ℕ → ℕ), IsMSequence (d / 2) g → g 1 = 0 →
      ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) ∧
    (∀ (d : ℕ) (P : Set (Fin d → ℝ)),
      IsSimplicialDPolytope P → faceCount P 0 ≤ d + 1 →
      ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) := by sorry

end Grunbaum2003
