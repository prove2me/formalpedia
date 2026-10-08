-- Prove2me | Theorems.Thm_MetricGenerators_ConnectedJoin_three_point
-- name    : MetricGenerators.ConnectedJoin.three_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:49:18.685086+00:00
-- url     : https://prove2.me/theorems/f69f2282-b18d-4332-a105-0139d89bca4c
-- title:
--   §3.2, p. 391 — in any realization, the distance from x to the y–z path is ½(μ(x, y) + μ(x, z) − μ(y, z))
-- statement:
--   Let $\mu:X\times X\to\mathbb N$ and let $(A,g)$ be a realization of $\mu$: $A$ is a tree and $d_A(g(x),g(y))=\mu(x,y)$ for all $x,y\in X$. Let $x,y,z\in X$ and let $w$ be a vertex of the path of $A$ between $g(y)$ and $g(z)$ that is nearest to $g(x)$ among the vertices of that path. Then
--
--   $$d_A\bigl(g(x),w\bigr)=\mu(x,y,z):=\tfrac12\bigl(\mu(x,y)+\mu(x,z)-\mu(y,z)\bigr).$$
--
--   So the length of the path joining $g(x)$ to the $g(y)$–$g(z)$ path is determined by $\mu$, independently of the realization. The paper uses this quantity in its inductive construction of the minimal realization of a tree metric.
--
--   **Formalization Note.** The vertices of the path of the tree $A$ between $g(y)$ and $g(z)$ are the vertices $w$ with $d_A(g(y),w)+d_A(w,g(z))=d_A(g(y),g(z))$. The identity is stated multiplied by $2$ and with the subtraction moved to the other side, $2\,d_A(g(x),w)+\mu(y,z)=\mu(x,y)+\mu(x,z)$, to avoid division and truncated subtraction on $\mathbb N$. A nearest vertex $w$ always exists, since the path is finite and nonempty.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 391, §3.2 (unnumbered display)

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TreeMetric

namespace MetricGenerators.ConnectedJoin

/-- **§3.2, p. 391 (unnumbered display).** "for any tree A realizing μ and for any x, y, z ∈ X,
the length of the path joining x and the path between y and z in A is determined by
μ(x, y, z) = ½(μ(x, y) + μ(x, z) − μ(y, z)), independently of the realization." (Sebő and
Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004),
DOI 10.1287/moor.1030.0070, p. 391.)

Let `(A, g)` be a realization of `μ : X → X → ℕ` and `x, y, z ∈ X`. If `w` is a vertex of the
path of `A` between `g y` and `g z` at minimum distance from `g x` among the vertices of that path,
then `2 · d_A(g x, w) + μ(y, z) = μ(x, y) + μ(x, z)`.

**Formalization Note.** The vertices of the `g y`–`g z` path of the tree `A` are the vertices `w`
with `d_A(g y, w) + d_A(w, g z) = d_A(g y, g z)` (in a tree the path is unique). The length of the
path joining `g x` to that path is `d_A(g x, w)` for a nearest such `w` (one exists: the path is
finite and nonempty). The halving and the subtraction are multiplied out, to avoid `ℕ` division
and truncated subtraction. -/
theorem three_point {X : Type*} (μ : X → X → ℕ) {N : ℕ} (A : SimpleGraph (Fin N))
    (g : X → Fin N) (hA : IsRealization μ A g) (x y z : X) (w : Fin N)
    (hw : A.dist (g y) w + A.dist w (g z) = A.dist (g y) (g z))
    (hmin : ∀ w' : Fin N, A.dist (g y) w' + A.dist w' (g z) = A.dist (g y) (g z) →
      A.dist (g x) w ≤ A.dist (g x) w') :
    2 * A.dist (g x) w + μ y z = μ x y + μ x z := by sorry

end MetricGenerators.ConnectedJoin
