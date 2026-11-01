-- Prove2me | Theorems.Thm_Grunbaum2003_polytopeFace_trichotomy_codim_two
-- name    : Grunbaum2003.polytopeFace_trichotomy_codim_two
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:14:28.704134+00:00
-- url     : https://prove2.me/theorems/6c6f8d6a-d6f8-4386-b58b-323fcde9d850
-- title:
--   Codimension-two trichotomy for exposed faces of a $d$-polytope
-- statement:
--   This lemma classifies every exposed face of a $d$-polytope in positive ambient dimension $d > 0$ relative to the $(d-2)$-skeleton.
--
--   Let $d > 0$ be a positive integer, let $P \subseteq \mathbb{R}^d$ be any subset, and let $F \in \mathcal{F}(P)$ be an exposed face of $P$ (`PolytopeFace P`). Write $\dim(F) = \operatorname{finrank}_{\mathbb{R}}\bigl(\operatorname{dir}(\operatorname{aff} F)\bigr)$ for the affine dimension of $F$. Then at least one of the following three alternatives holds:
--
--   $$
--   \bigl(F = \emptyset \;\lor\; \dim(F) \le d - 2\bigr) \;\lor\; F = P \;\lor\; \bigl(F \ne \emptyset \;\land\; \dim(F) = d - 1\bigr).
--   $$
--
--   That is, every exposed face of $P$ either belongs to the $(d-2)$-skeleton $\operatorname{skel}_{d-2}(P)$, coincides with the improper face $P$ itself, or is a nonempty facet of dimension $d - 1$.
--
--   This trichotomy is a key structural step in reconstructing the full face lattice $\mathcal{F}(P)$ from the $(d-2)$-skeleton (or from the graph when $d \le 3$): since $\operatorname{skel}_{d-2}(P)$ and the improper face $P$ are already known, only the facets ($\dim(F) = d - 1$) need to be recovered from lower-dimensional skeleton data.
--
--   **Formalization Note** When $\dim(F) = d$ and $F \ne \emptyset$, the direction submodule of $\operatorname{aff}(F)$ equals all of $\mathbb{R}^d$, forcing any linear functional exposing $F$ in $P$ to be constant on $\mathbb{R}^d$ and hence $F = P$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.1 & §12.1, pp. 26–30, 225–226

import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem polytopeFace_trichotomy_codim_two (d : ℕ) (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (F : PolytopeFace P) :
    (F.val = ∅ ∨ Module.finrank ℝ (affineSpan ℝ F.val).direction ≤ d - 2) ∨
      F.val = P ∨
      (F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1) := by sorry

end Grunbaum2003
