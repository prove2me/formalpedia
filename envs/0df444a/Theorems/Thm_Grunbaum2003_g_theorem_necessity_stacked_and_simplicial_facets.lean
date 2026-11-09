-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_necessity_stacked_and_simplicial_facets
-- name    : Grunbaum2003.g_theorem_necessity_stacked_and_simplicial_facets
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T01:59:29.077684+00:00
-- url     : https://prove2.me/theorems/95a04bec-341d-4e7d-be92-53a54549a1e6
-- title:
--   Simplicial facet subface bijection and necessity for stacked polytopes ($g(2) = 0$)
-- statement:
--   Let $P \subset \mathbb{R}^d$ be a simplicial $d$-polytope.
--
--   1. Every facet $F$ of $P$ ($\dim F = d - 1$) is the convex hull of an affinely independent, injective family $v_0,\dots,v_{d-1}$ of $d$ exposed vertices of $P$, and the map $s \mapsto \operatorname{conv}\{v_i : i \in s\}$ is an injective correspondence between vertex subsets $s \subseteq \{0,\dots,d-1\}$ and subfaces satisfying $\operatorname{conv}\{v_i : i \in s\} \cap \operatorname{ext} P = \{v_i : i \in s\}$.
--   2. For $d \ge 4$ and $f_0(P) > d + 1$, if $P$ has the stacked-polytope face vector
--
--   $$
--   f_j(P) = \binom{d+1}{j+1} + \bigl(f_0(P) - (d+1)\bigr)\,M_{d,1,j+1} \qquad (0 \le j < d),
--   $$
--
--   then $g = (1, f_0(P) - (d+1), 0, 0, \dots)$ is an $M$-sequence of length $\lfloor d/2 \rfloor$ satisfying the $g$-theorem necessity equation for $P$.
--
--   This proves the $g(2) = 0$ necessity branch and provides the unconditional simplicial facet subface bijection.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed.), §10.6, pp. 198a–198b (PDF 235–236)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem g_theorem_necessity_stacked_and_simplicial_facets :
    (∀ {d : ℕ} {P : Set (Fin d → ℝ)},
      IsSimplicialDPolytope P →
      ∀ (F : Set (Fin d → ℝ)), F.Nonempty → IsExposed ℝ P F →
        Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d →
        ∃ v : Fin d → Fin d → ℝ,
          AffineIndependent ℝ v ∧
          Function.Injective v ∧
          (∀ i : Fin d, IsExposed ℝ P {v i}) ∧
          F = convexHull ℝ (Set.range v) ∧
          F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = Set.range v ∧
          (F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}).ncard = d ∧
          (∀ s : Finset (Fin d),
            convexHull ℝ (v '' (s : Set (Fin d))) ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} =
              v '' (s : Set (Fin d))) ∧
          (∀ s₁ s₂ : Finset (Fin d),
            convexHull ℝ (v '' (s₁ : Set (Fin d))) = convexHull ℝ (v '' (s₂ : Set (Fin d))) ↔
              s₁ = s₂)) ∧
    (∀ (d : ℕ), 4 ≤ d → ∀ (P : Set (Fin d → ℝ)),
      IsSimplicialDPolytope P →
      d + 1 < faceCount P 0 →
      (∀ j : Fin d, (faceCount P j.val : ℤ) =
        (Nat.choose (d + 1) j.succ.val : ℤ) +
          ((faceCount P 0 - (d + 1) : ℕ) : ℤ) * gTheoremMatrix d 1 j.succ.val) →
      ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        g 1 = faceCount P 0 - (d + 1) ∧
        g 2 = 0 ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) := by sorry

end Grunbaum2003
