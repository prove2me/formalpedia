-- Prove2me | Theorems.Thm_Grunbaum2003_polytope_normalized_halfspace_presentation_and_facet_lower_bound
-- name    : Grunbaum2003.polytope_normalized_halfspace_presentation_and_facet_lower_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:30.388803+00:00
-- url     : https://prove2.me/theorems/6bf22b51-2bf3-43ff-988d-f2bc4fa3a6be
-- title:
--   Normalized finite facet H-representation and $f_{d-1}(P) \ge d + 1$ for $d$-polytopes with $0 \in \operatorname{int}(P)$
-- statement:
--   This theorem establishes the normalized finite facet halfspace representation (`P = {x | ∀ i, L i x ≤ 1}`) and the facet-count lower bound $f_{d-1}(P) \ge d + 1$ for any $d$-polytope $P \subseteq \mathbb{R}^d$ ($d \ge 1$) containing the origin in its interior.
--
--   Let $d \ge 1$ be a positive integer, let $P \subseteq \mathbb{R}^d$ be a $d$-polytope (`IsDPolytope P`) with $0 \in \operatorname{int}(P)$, and let `oracle` be a ray-shooting oracle for $P$ (`IsPolytopeRayOracle P oracle`). Then:
--   1. **Facet count lower bound (`dimension_add_one_le_original_facet_count`):** $P$ has at least $d + 1$ facets:
--      $$
--      d + 1 \le f_{d-1}(P) = \operatorname{faceCount}(P, d - 1).
--      $$
--   2. **Normalized H-representation (`normalized_halfspaces_indexed_by_facet_count`):** There exists a family of $f_{d-1}(P)$ continuous linear functionals $L : \operatorname{Fin}(f_{d-1}(P)) \to (\mathbb{R}^d)^*$ such that
--      $$
--      P = \{x \in \mathbb{R}^d \mid \forall i,\; L_i(x) \le 1\},
--      $$
--      and for every index $i$, either $L_i = 0$ or the level set $\{x \in P \mid L_i(x) = 1\}$ is a facet of $P$ (nonempty, exposed in $P$, and of affine dimension $d - 1$).
--
--   **Formalization Note** Normalizing each facet inequality $a_i(x) \le b_i$ by $b_i > a_i(0) = 0$ puts $P$ in the gauge form $\{x \mid \max_i L_i(x) \le 1\}$ used by the Gritzmann–Klee–Westwater planar secant analysis, while boundedness of $P$ forces the differences $L_{i+1} - L_0$ to have trivial common kernel, giving $f_{d-1}(P) \ge d + 1$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.1, pp. 31–33 & §3.6, pp. 52b–52c

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

set_option autoImplicit false

namespace Grunbaum2003

theorem polytope_normalized_halfspace_presentation_and_facet_lower_bound
    (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (horacle : IsPolytopeRayOracle P oracle) :
    d + 1 ≤ faceCount P (d - 1) ∧
    ∃ L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ,
      P = {x | ∀ i, L i x ≤ 1} ∧
      ∀ i, L i = 0 ∨
        ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
          Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1) := by sorry

end Grunbaum2003
