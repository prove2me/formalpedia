-- Prove2me | Theorems.Thm_KServer_workFnU_push
-- name    : KServer.workFnU_push
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T17:40:11.683391+00:00
-- url     : https://prove2.me/theorems/29c752b4-3f7f-4e6f-8fdc-dda59e9cb823
-- title:
--   Pushing a witness of the shadow outwards along a geodesic
-- statement:
--   Suppose $b$ lies on a geodesic from $p$ to $u$, that is, $pb + bu = pu$. Then in the expression $pb + pb' - w(b,b')$ the point $b$ may be replaced by the further point $u$:
--
--   $$pb + pb' - w(b,b') \;\le\; pu + pb' - w(u,b').$$
--
--   ## Role
--
--   This is the workhorse of the geometric half of the Bein–Chrobak–Larmore analysis. The expressions defining the potentials $\Psi$, $\Lambda$ and $\Gamma$ are suprema over free points, and the plan for showing $\Lambda, \Gamma \le \Psi$ in the city-block plane is to push every free point out to a corner of a bounding rectangle, after which only finitely many configurations remain. This lemma is the single step of that push: since every point of an axis-parallel rectangle lies between any given point and some corner, one application per free point suffices.
--
--   The proof is one line of arithmetic on top of the Lipschitz property. Substituting $pb = pu - bu$ and using $w(u,b') \le w(b,b') + bu$,
--
--   $$pb - w(b,b') \;=\; pu - bu - w(b,b') \;\le\; pu - w(u,b').$$
--
--   The cost $bu$ of moving the server from $b$ to $u$ is exactly the length that the detour through $b$ saves, so the two cancel.
--
--   **Formalization note.** The matching cost between the configurations $\{r,b,b'\}$ and $\{r,u,b'\}$ is $d(r,r) + d(b,u) + d(b',b') = bu$, which is what reduces the Lipschitz property to the displayed form.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 4: 'Point b must be located between p and some corner of R, say y, that is, pb = py - by. Then pb - w(b,b') = py - by - w(b,b') <= py - w(y,b') by the Lipschitz property of w.'

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_push (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r p b b' u : M) (h : dist p b + dist b u = dist p u) :
    dist p b + dist p b' - workFnU C₀ σ ![r, b, b']
      ≤ dist p u + dist p b' - workFnU C₀ σ ![r, u, b'] := by sorry

end KServer
