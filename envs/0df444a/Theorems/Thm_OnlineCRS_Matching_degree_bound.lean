-- Prove2me | Theorems.Thm_OnlineCRS_Matching_degree_bound
-- name    : OnlineCRS.Matching.degree_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:31.254434+00:00
-- url     : https://prove2.me/theorems/371e9bca-4a8a-476a-be09-6bffae58caaf
-- title:
--   Proof of Theorem 2.7, p. 14 — x ∈ bP_G gives Σ_{g∈δ(u)∪δ(v)∖{g′}} x_g ≤ 2(b − x_{g′})
-- statement:
--   Let $G=(V,E)$ be a finite loopless graph, let $b\in[0,1]$, let $x\in bP_G$, and let $g'\in E$ have ends $u,v$. Then
--
--   $$\sum_{g\in(\delta(u)\cup\delta(v))\setminus\{g'\}}x_g\ \le\ 2\,(b-x_{g'}).$$
--
--   The degree constraints of $bP_G$ at $u$ and at $v$ bound the weight of $\delta(u)\setminus\{g'\}$ and of $\delta(v)\setminus\{g'\}$ by $b-x_{g'}$ each; this gives the first inequality of the final chain in the proof of Theorem 2.7.
--
--   **Formalization Note** $bP_G$ is the pointwise scaling $\{by:y\in P_G\}$, so $b=0$ is included. Parallel copies of $g'$ lie in both $\delta(u)$ and $\delta(v)$ but are counted once in the union, which only helps the bound.
-- source:
--   arXiv:1508.00142v2, proof of Theorem 2.7, pp. 13–14, first inequality of the display and the sentence after it

import Mathlib
import Definitions.Def_OnlineCRS_Matching_Model

namespace OnlineCRS.Matching

open scoped Pointwise

/-- Proof of Theorem 2.7, pp. 13–14: the union of the two endpoint neighborhoods. -/
theorem degree_bound {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (x : E → ℝ)
    (hx : x ∈ b • matchingRelax G) (g : E) (u v : V)
    (hg : G.ends g = s(u, v)) :
    ∑ h ∈ otherIncident G u v g, x h ≤ 2 * (b - x g) := by sorry

end OnlineCRS.Matching
