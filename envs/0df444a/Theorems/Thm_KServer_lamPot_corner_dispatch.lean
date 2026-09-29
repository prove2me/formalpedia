-- Prove2me | Theorems.Thm_KServer_lamPot_corner_dispatch
-- name    : KServer.lamPot_corner_dispatch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T18:29:27.858529+00:00
-- url     : https://prove2.me/theorems/036239bd-d673-49c2-82b8-430102e89de7
-- title:
--   The corner case analysis for the auxiliary potential Lambda
-- statement:
--   Let $x, z, y, t$ be four points of a metric space, thought of as the corners of a rectangle listed clockwise, so that $\{x,y\}$ and $\{z,t\}$ are its diagonals. Suppose two further points $p$ and $q$ each lie on **both** diagonals:
--
--   $$xp + py = xy, \qquad zp + pt = zt, \qquad xq + qy = xy, \qquad zq + qt = zt.$$
--
--   Then, whenever $b, b', c, c'$ are among the four corners and $\{e,e'\}$ is one of the two diagonals, the corresponding instance of the auxiliary potential is dominated by the lazy potential:
--
--   $$\bigl(-rp + pb + pb' - w(b,b')\bigr) + \bigl(-rq + qc + qc' - w(c,c')\bigr) - w(p,q) + ee' - w(e,e') \;\le\; \Psi_{w,r}.$$
--
--   ## Role
--
--   This is the combinatorial core of the proof that $\Lambda_{w,r} \le \Psi_{w,r}$ in the city-block plane, isolated from the geometry. The plane is used only to produce the rectangle and to push the free points out to its corners; once that is done, what remains is the present statement, and it holds in **any** metric space with four points and two further points placed as described.
--
--   The proof is the exhaustive case analysis: over the $4^4$ assignments of corners to $b, b', c, c'$ and the four choices of diagonal for $(e,e')$, each of the $1024$ configurations is settled by one of the seven configuration lemmas — according to whether $b$ and $b'$ land in opposite corners, in the same corner, or in adjacent corners, and correspondingly for $c$ and $c'$. No configuration is left over, and the coverage is verified case by case rather than by an appeal to symmetry.
--
--   **Formalization note.** Each case is reached after at most a few of the four symmetries of the expression — interchanging $b$ with $b'$, $c$ with $c'$, $e$ with $e'$, or the two triples $(p,b,b')$ and $(q,c,c')$ with each other — every one of which is an identity following from the invariance of the work function under permuting a configuration. The betweenness hypotheses that the configuration lemmas require are, in each case, exactly one of the sixteen instances of the four displayed diagonal identities, established once before the split.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Lemma 5, the case analysis following formula (7): 'where b', c, c', e, e' are in {x,z,y,t} and {e,e'} = {x,y} or {z,t}. We consider a number of cases, depending on which points are in which corners.'

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem lamPot_corner_dispatch (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r x z y t p q : M)
    (hp1 : dist x p + dist p y = dist x y) (hp2 : dist z p + dist p t = dist z t)
    (hq1 : dist x q + dist q y = dist x y) (hq2 : dist z q + dist q t = dist z t)
    (B B' C C' E E' : M)
    (hB : B = x ∨ B = z ∨ B = y ∨ B = t)
    (hB' : B' = x ∨ B' = z ∨ B' = y ∨ B' = t)
    (hC : C = x ∨ C = z ∨ C = y ∨ C = t)
    (hC' : C' = x ∨ C' = z ∨ C' = y ∨ C' = t)
    (hEE : (E = x ∧ E' = y) ∨ (E = z ∧ E' = t) ∨ (E = y ∧ E' = x) ∨ (E = t ∧ E' = z)) :
    (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
      + (-dist r q + (dist q C + dist q C' - workFnU C₀ σ ![r, C, C']))
      - workFnU C₀ σ ![r, p, q] + dist E E' - workFnU C₀ σ ![r, E, E']
      ≤ lazyPot C₀ σ r := by sorry

end KServer
