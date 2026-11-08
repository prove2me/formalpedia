-- Prove2me | Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
-- name    : Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T01:30:21.317442+00:00
-- url     : https://prove2.me/theorems/c2e5cd91-5bb0-4616-b353-79dc2337d29b
-- title:
--   Identification of $f_0(P)$ with singleton exposed vertices and sharp lower bound $f_0(P) \ge d + 1$ for $d$-polytopes
-- statement:
--   For every subset $P \subseteq \mathbb{R}^d$, a nonempty exposed face $F \subseteq P$ has affine direction dimension $0$ if and only if $F = \{x\}$ is a singleton exposed vertex, so the zero-dimensional face count satisfies
--   $$
--   f_0(P) = \operatorname{faceCount}(P, 0) = \#\{x \in \mathbb{R}^d \mid \operatorname{IsExposed}_{\mathbb{R}}(P, \{x\})\}.
--   $$
--   Furthermore, if $P \subseteq \mathbb{R}^d$ is a full-dimensional $d$-polytope (`IsDPolytope P`), then $f_0(P) \ge d + 1$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.1, pp. 31–36

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound :
  ∀ (d : ℕ) (P : Set (Fin d → ℝ)),
    faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
    (IsDPolytope P → d + 1 ≤ faceCount P 0) := by sorry

end Grunbaum2003
