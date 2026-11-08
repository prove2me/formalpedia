-- Prove2me | Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
-- name    : Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T02:14:52.693205+00:00
-- url     : https://prove2.me/theorems/1a71cf03-6bc8-40c1-929b-ef37daa7805b
-- title:
--   Two-vertex characterization of $1$-dimensional exposed faces, automatic simpliciality of $2$-polytopes, and binomial face counts of $d$-simplices
-- statement:
--   This theorem establishes three foundational geometric results for $f$-vectors of simplicial polytopes:
--   1. **Two-Vertex Characterization of $1$-Dimensional Exposed Faces:** Under the exposed-vertex hull representation, a nonempty exposed face $F$ of $P \subseteq \mathbb{R}^d$ has $\operatorname{finrank}_{\mathbb{R}}(\operatorname{aff}(F).\mathrm{direction}) = 1$ if and only if $F \cap \operatorname{vert}(P) = \{a, b\}$ for two distinct exposed vertices $a \ne b$ of $P$ and $F = \operatorname{conv}\{a, b\}$.
--   2. **Automatic Simpliciality in Dimension $2$:** For every subset $P \subseteq \mathbb{R}^2$, `IsSimplicialDPolytope P ↔ IsDPolytope P` (every facet of a $2$-polytope is a $1$-dimensional exposed face, hence the convex hull of $2$ affinely independent vertices).
--   3. **Simpliciality and Binomial Face Counts of $d$-Simplices:** For every $d \in \mathbb{N}$ and every affinely independent family $v : \operatorname{Fin}(d+1) \to \mathbb{R}^d$ (in particular the standard $d$-simplex in $\mathbb{R}^d$), $P = \operatorname{conv}(\operatorname{range} v)$ satisfies `IsSimplicialDPolytope P` and
--      $$
--      \forall k \in \mathbb{N},\quad \operatorname{faceCount}(P, k) = \binom{d+1}{k+1}.
--      $$
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.1, §4.1, §4.5, pp. 31–36, 53–58

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent

set_option autoImplicit false

namespace Grunbaum2003

theorem exposed_edge_pair_and_simplex_faceCount_choose :
  (∀ {d : ℕ} {P : Set (Fin d → ℝ)},
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ∀ (F : Set (Fin d → ℝ)), IsExposed ℝ P F →
      ((F.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 1) ↔
        ∃ a b : Fin d → ℝ,
          IsExposed ℝ P {a} ∧ IsExposed ℝ P {b} ∧ a ≠ b ∧
          F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = {a, b} ∧
          F = convexHull ℝ ({a, b} : Set (Fin d → ℝ)))) ∧
  (∀ P : Set (Fin 2 → ℝ), IsSimplicialDPolytope P ↔ IsDPolytope P) ∧
  (∀ (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ),
    AffineIndependent ℝ v →
    IsSimplicialDPolytope (convexHull ℝ (Set.range v)) ∧
    ∀ k : ℕ, faceCount (convexHull ℝ (Set.range v)) k = Nat.choose (d + 1) (k + 1)) ∧
  (∀ d : ℕ,
    ∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ k : ℕ, faceCount P k = Nat.choose (d + 1) (k + 1)) := by sorry

end Grunbaum2003
