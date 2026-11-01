-- Prove2me | Theorems.Thm_Grunbaum2003_joswig_ziegler_cubical_realization_and_vertex_equiv
-- name    : Grunbaum2003.joswig_ziegler_cubical_realization_and_vertex_equiv
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T22:21:44.499722+00:00
-- url     : https://prove2.me/theorems/5c718720-dac8-4a93-a5c6-fd9c74bd0660
-- title:
--   Joswig–Ziegler neighborly cubical polytopes: vertex bijection ($d \le 3$) and higher-skeleton equivalence ($d \ge 4$)
-- statement:
--   This theorem decomposes the Joswig–Ziegler neighborly cubical realization theorem (Grünbaum §4.9, p. 69b) into the $0$-skeleton (vertex-equinumerosity) regime $d \in \{2, 3\}$ and the higher-dimensional skeleton regime $d \ge 4$.
--
--   Let $n > d \ge 2$ be integers, and let $C^n = [0, 1]^n \subseteq \mathbb{R}^n$ denote the standard $n$-cube (`standardCube n`). Then:
--
--   1. **Low-dimensional regime ($d \in \{2, 3\}$, where $\lfloor d/2 \rfloor - 1 = 0$):** There exists a cubical $d$-polytope $P \subseteq \mathbb{R}^d$ (`IsCubicalDPolytope P`) whose set of exposed vertices is in bijection with the set of exposed vertices of $C^n$:
--
--   $$
--   d \le 3 \implies \exists P \subseteq \mathbb{R}^d,\; \operatorname{IsCubicalDPolytope}(P) \;\land\; \bigl(\operatorname{vert}(P) \simeq \operatorname{vert}(C^n)\bigr);
--   $$
--
--   2. **Higher-dimensional regime ($d \ge 4$, where $\lfloor d/2 \rfloor - 1 \ge 1$):** There exists a cubical $d$-polytope $P \subseteq \mathbb{R}^d$ whose $(\lfloor d/2 \rfloor - 1)$-skeleton is order-isomorphic to that of $C^n$:
--
--   $$
--   d \ge 4 \implies \exists P \subseteq \mathbb{R}^d,\; \operatorname{IsCubicalDPolytope}(P) \;\land\; \bigl(\operatorname{skel}_{\lfloor d/2 \rfloor - 1}(P) \simeq_{\mathrm{ord}} \operatorname{skel}_{\lfloor d/2 \rfloor - 1}(C^n)\bigr).
--   $$
--
--   In `neighborly_cubical_realization`, when $2 \le d \le 3$, we have $\lfloor d/2 \rfloor - 1 = 0$, and applying `skeletonFace_zero_orderIso_of_exposed_vertices_equiv` to the vertex bijection $\operatorname{vert}(P) \simeq \operatorname{vert}(C^n)$ immediately constructs the $0$-skeleton order isomorphism $\operatorname{skel}_0(P) \simeq_{\mathrm{ord}} \operatorname{skel}_0(C^n)$.
--
--   **Formalization Note** For $d = 2$, a convex $2^n$-gon in $\mathbb{R}^2$ is a cubical $2$-polytope with $2^n = |\operatorname{vert}(C^n)|$ vertices; for $d = 3$, cubical $3$-polytopes with $2^n$ vertices exist for all $n \ge 4$, and for $d \ge 4$ the deformed-product construction of Joswig and Ziegler (2000) preserves the full $(\lfloor d/2 \rfloor - 1)$-skeleton of $C^n$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §4.9, p. 69b (citing Joswig–Ziegler 2000)

import Definitions.Def_Grunbaum2003_IsCubicalDPolytope
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_standardCube
import Mathlib.Analysis.Convex.Exposed

set_option autoImplicit false

namespace Grunbaum2003

theorem joswig_ziegler_cubical_realization_and_vertex_equiv (n d : ℕ)
    (hd : 2 ≤ d) (hnd : d < n) :
    (d ≤ 3 → ∃ P : Set (Fin d → ℝ), IsCubicalDPolytope P ∧
      Nonempty ({x : Fin d → ℝ | IsExposed ℝ P {x}} ≃
        {y : Fin n → ℝ | IsExposed ℝ (standardCube n) {y}})) ∧
    (4 ≤ d → ∃ P : Set (Fin d → ℝ), IsCubicalDPolytope P ∧
      Nonempty (SkeletonFace P (d / 2 - 1) ≃o
        SkeletonFace (standardCube n) (d / 2 - 1))) := by sorry

end Grunbaum2003
