-- Prove2me | Theorems.Thm_OAI_Problem160_exists_unit_distance_coloring_of_center_cover
-- name    : OAI.Problem160.exists_unit_distance_coloring_of_center_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T17:39:47.411583+00:00
-- url     : https://prove2.me/theorems/fe1301eb-e191-4de4-a458-18ed295eb2b4
-- title:
--   Proper unit-distance colorings from colored covers by small, well-separated cells
-- statement:
--   Let $(X,d)$ be a pseudometric space, let $I$ be an arbitrary index set, and let $k\in\mathbb{N}$. Suppose we are given centers $z:I\to X$, a coloring of the indices $\kappa:I\to\{0,1,\dots,k-1\}$ and a real number $r$ such that
--
--   1. (covering) for every $x\in X$ there is $i\in I$ with $d(x,z_i)\le r$;
--   2. (small cells) $2r<1$;
--   3. (separation) for all $i,j\in I$ with $i\ne j$ and $\kappa(i)=\kappa(j)$ one has $d(z_i,z_j)>1+2r$.
--
--   Then the points of $X$ can be colored with $k$ colors so that points at distance exactly $1$ get different colors:
--   $$\exists\, c:X\to\{0,1,\dots,k-1\}\quad \forall\, x,y\in X:\qquad d(x,y)=1\ \Longrightarrow\ c(x)\ne c(y).$$
--
--   This is the abstract cell argument behind tiling-type colorings of the plane: cover the space by closed balls of radius $r$ (diameter below $1$), color the balls so that equally colored balls are far apart, and give each point the color of one ball containing it. The balls may overlap and need not form a partition, and the conclusion asserts only the existence of $c$, with no measurability or regularity.
--
--   **Formalization Note** The colors form `Fin k`, and the three hypotheses are `hcover`, `hdiam` and `hsep`. No sign condition is imposed on $r$ (if $X$ is nonempty, the covering hypothesis forces $r\ge0$). Separation is required for distinct indices $i\ne j$, not merely for distinct centers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/PlaneColoring/Assembly.lean#L9-L37

import Mathlib
import Definitions.Def_PlaneColoring

open OAI OAI.Problem160

theorem OAI.Problem160.exists_unit_distance_coloring_of_center_cover
    {X I : Type*} [PseudoMetricSpace X] {k : ℕ}
    (center : I → X) (color : I → Fin k) (r : ℝ)
    (hcover : ∀ x : X, ∃ i : I, dist x (center i) ≤ r)
    (hdiam : 2 * r < 1)
    (hsep : ∀ i j : I, i ≠ j → color i = color j →
      1 + 2 * r < dist (center i) (center j)) :
    ∃ c : X → Fin k, ∀ x y : X, dist x y = 1 → c x ≠ c y := by sorry
