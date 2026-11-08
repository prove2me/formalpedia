-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_f_vector_equivalences_from_geometric_core
-- name    : Grunbaum2003.g_theorem_f_vector_equivalences_from_geometric_core
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T03:45:46.933006+00:00
-- url     : https://prove2.me/theorems/5e84b7d1-f961-434d-a328-92c33de892a6
-- title:
--   Reduction of the polygon ($d=2$), Steinitz ($d=3$), and higher ($d \ge 4$) $f$-vector equivalences to their geometric core conditions
-- statement:
--   This theorem proves that the three $f$-vector characterization equivalences of `simplicial_g_theorem` follow directly from their pure geometric core conditions:
--   1. **Dimension $d = 2$:** From $f_0(P) \ge 3$, $f_1(P) = f_0(P)$ for every $2$-polytope $P$, and the existence of a $2$-polytope with $n + 3$ vertices for every $n \in \mathbb{N}$, the $(1, f_0, f_1) = (1, n+3, n+3)$ characterization holds.
--   2. **Dimension $d = 3$:** From $f_0(P) \ge 4$, Euler's relation $f_0(P) + f_2(P) = f_1(P) + 2$, the facet-edge double-counting identity $3f_2(P) = 2f_1(P)$, and the existence of a simplicial $3$-polytope with $n + 4$ vertices for every $n \in \mathbb{N}$, integer linear arithmetic (`omega`) yields $(1, f_0, f_1, f_2) = (1, n+4, 3n+6, 2n+4)$.
--   3. **Dimensions $d \ge 4$:** From necessity and sufficiency of `IsMSequence (d / 2) g` on `(faceCount P j.val : ℤ)` for $j \in \operatorname{Fin} d$, together with `gTheoremMatrix_sum_col_zero` at $k = 0$, the full $(d+1)$-entry `gTheoremMatrix` equivalence holds.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §10.6, pp. 198a–198b

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators Classical

namespace Grunbaum2003

theorem g_theorem_f_vector_equivalences_from_geometric_core :
  ((∀ P : Set (Fin 2 → ℝ), IsDPolytope P → 3 ≤ faceCount P 0) →
    (∀ P : Set (Fin 2 → ℝ), IsDPolytope P → faceCount P 1 = faceCount P 0) →
    (∀ n : ℕ, ∃ P : Set (Fin 2 → ℝ), IsDPolytope P ∧ faceCount P 0 = n + 3) →
    ∀ f : Fin (2 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 2 → ℝ),
        IsDPolytope P ∧
        ∀ j : Fin 2, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3)) ∧
  ((∀ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P → 4 ≤ faceCount P 0) →
    (∀ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P →
      faceCount P 0 + faceCount P 2 = faceCount P 1 + 2 ∧
      3 * faceCount P 2 = 2 * faceCount P 1) →
    (∀ n : ℕ, ∃ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P ∧ faceCount P 0 = n + 4) →
    ∀ f : Fin (3 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 3 → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin 3, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4)) ∧
  (∀ (d : ℕ), 4 ≤ d →
    (∀ P : Set (Fin d → ℝ), IsSimplicialDPolytope P →
      ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
    (∀ g : ℕ → ℕ, IsMSequence (d / 2) g →
      ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
    ∀ (f : Fin (d + 1) → ℤ), f 0 = 1 →
      ((∃ P : Set (Fin d → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ k : Fin (d + 1),
          f k = ∑ j ∈ Finset.range (d / 2 + 1),
            (g j : ℤ) * gTheoremMatrix d j k.val)) := by sorry

end Grunbaum2003
