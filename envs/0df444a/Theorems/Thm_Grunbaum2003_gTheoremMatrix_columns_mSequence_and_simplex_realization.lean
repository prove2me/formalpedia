-- Prove2me | Theorems.Thm_Grunbaum2003_gTheoremMatrix_columns_mSequence_and_simplex_realization
-- name    : Grunbaum2003.gTheoremMatrix_columns_mSequence_and_simplex_realization
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T02:33:55.620806+00:00
-- url     : https://prove2.me/theorems/affbd82f-46e5-44c4-9dc3-a4ced45d5033
-- title:
--   Björner $g$-theorem matrix columns, $M$-sequence characterizations, and $d$-simplex realization for all $d \in \mathbb{N}$
-- statement:
--   This theorem proves the fundamental algebraic and combinatorial properties of Björner's $g$-theorem matrix $M_d$ (`gTheoremMatrix`) and Macaulay $M$-sequences (`IsMSequence`):
--   1. Row $j = 0$ of $M_d$ is $M_d(0, k) = \binom{d+1}{k}$ for all $0 \le k \le d$.
--   2. For any $g : \mathbb{N} \to \mathbb{N}$ with $g(0) = 1$, the $k = 0$ column sum is $\sum_{j=0}^{\lfloor d/2 \rfloor} g(j) M_d(j, 0) = 1$, and for $d \ge 2$ the $k = 1$ column sum is $\sum_{j=0}^{\lfloor d/2 \rfloor} g(j) M_d(j, 1) = (d + 1) + g(1)$.
--   3. Every sequence of the form $g = (1, n, 0, 0, \dots)$ satisfies `IsMSequence m g` for all $m, n \in \mathbb{N}$, and for $m = 1$ (`d = 2` and `d = 3`), `IsMSequence 1 g ↔ g 0 = 1`.
--   4. Every dimension $d \in \mathbb{N}$ admits a simplicial $d$-polytope (the $d$-simplex $\Delta^d$) whose augmented $f$-vector realizes the $M_d$-transform of the $M$-sequence $g = (1, 0, 0, \dots)$.
--   5. In dimensions $d = 2$ and $d = 3$, the $M_d$-transform conditions for `IsMSequence (d / 2) g` are equivalent to the explicit parametric forms $(1, n + 3, n + 3)$ and $(1, n + 4, 3n + 6, 2n + 4)$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §10.6, pp. 198a–198b

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem gTheoremMatrix_columns_mSequence_and_simplex_realization :
  (∀ (d : ℕ) (k : Fin (d + 1)),
    gTheoremMatrix d 0 k.val = (Nat.choose (d + 1) k.val : ℤ)) ∧
  (∀ (d : ℕ) (g : ℕ → ℕ), g 0 = 1 →
    (∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 0) = 1) ∧
  (∀ (d : ℕ), 2 ≤ d → ∀ (g : ℕ → ℕ), g 0 = 1 →
    (∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 1) =
      (d + 1 : ℤ) + (g 1 : ℤ)) ∧
  (∀ m n : ℕ,
    IsMSequence m (fun j => if j = 0 then 1 else if j = 1 then n else 0)) ∧
  (∀ g : ℕ → ℕ, IsMSequence 1 g ↔ g 0 = 1) ∧
  (∀ d : ℕ,
    ∃ (P : Set (Fin d → ℝ)) (g : ℕ → ℕ),
      IsSimplicialDPolytope P ∧
      IsMSequence (d / 2) g ∧
      g 1 = 0 ∧
      (∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1),
          (g i : ℤ) * gTheoremMatrix d i j.succ.val)) ∧
  (∀ f : Fin (2 + 1) → ℤ, f 0 = 1 →
    ((∃ g : ℕ → ℕ, IsMSequence (2 / 2) g ∧
      ∀ k : Fin (2 + 1),
        f k = ∑ j ∈ Finset.range (2 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 2 j k.val) ↔
     (∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3))) ∧
  (∀ f : Fin (3 + 1) → ℤ, f 0 = 1 →
    ((∃ g : ℕ → ℕ, IsMSequence (3 / 2) g ∧
      ∀ k : Fin (3 + 1),
        f k = ∑ j ∈ Finset.range (3 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 3 j k.val) ↔
     (∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4))) := by sorry

end Grunbaum2003
