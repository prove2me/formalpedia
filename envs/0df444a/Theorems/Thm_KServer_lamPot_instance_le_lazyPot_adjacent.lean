-- Prove2me | Theorems.Thm_KServer_lamPot_instance_le_lazyPot_adjacent
-- name    : KServer.lamPot_instance_le_lazyPot_adjacent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T17:52:45.608941+00:00
-- url     : https://prove2.me/theorems/ce41de70-3a50-47f3-b634-3b0fac02a1de
-- title:
--   Four further configurations in which an instance of Lambda is below the lazy potential
-- statement:
--   Continuing the analysis of the auxiliary potential $\Lambda_{w,r}$, an instance of $\Lambda_{w,r}$ is bounded by the lazy potential $\Psi_{w,r}$ in each of four further configurations of its witnesses, again in an **arbitrary** metric space:
--
--   1. $b = b'$, $c = c'$, $e' = b$, and $p$ lies on a geodesic between $e$ and $b$;
--   2. $q$ lies on a geodesic between $c$ and $b$, and also on a geodesic between $b'$ and $c'$;
--   3. $c = b$, and $q$ lies on a geodesic between $b'$ and $c'$;
--   4. $c = b$ and $c' = b'$, with $e' = b$ and $e$ arbitrary.
--
--   ## Role
--
--   Together with the three configurations treated separately, these exhaust the case analysis by which $\Lambda_{w,r} \le \Psi_{w,r}$ is proved in the city-block plane. In that application every free point has first been pushed out to a corner of a bounding rectangle, and the hypotheses above are what the rectangle then supplies: statements 2 and 3 are the cases where $b$ and $b'$ land in *adjacent* corners, the betweenness hypotheses being the two diagonals of the rectangle, on both of which every interior point lies; statement 1 is the case where $b, b'$ and $c, c'$ each collapse to a single corner; statement 4 is the case where the two pairs land in the same two adjacent corners.
--
--   Two of the four need the quasiconvexity inequality, which delivers a minimum of two rematchings and so splits the argument. In statement 4 the two branches are exchanged by interchanging $p$ and $q$, under which the expression is invariant because the two triples carry the same pair of points. In statement 2 no such symmetry is available — interchanging $c$ with $c'$ leaves the expression unchanged, and interchanging the two triples would require betweenness along a side of the rectangle rather than a diagonal — but the branches nevertheless both close, on *different* instances of $\Psi_{w,r}$ obtained from one another by simultaneously interchanging $b$ with $b'$ and $c$ with $c'$. Statement 3 needs no quasiconvexity at all.
--
--   **Formalization note.** Each statement reduces to a single linear-arithmetic combination of one instance of $\Psi_{w,r}$, a few triangle inequalities, at most one application of the Lipschitz property in pinned two-point form, and at most one application of pairwise quasiconvexity. Where a quasiconvexity branch must be handled by a symmetry, the case is factored through an auxiliary statement taking the branch as a hypothesis, which is then applied twice with permuted arguments; this keeps the argument non-circular.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Lemma 5, Cases 2.3, 3.1, 3.2 and 3.3.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem lamPot_instance_le_lazyPot_adjacent (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M) (r : M) :
    (∀ p q B C E : M, dist E p + dist p B = dist E B →
      (-dist r p + (dist p B + dist p B - workFnU C₀ σ ![r, B, B]))
        + (-dist r q + (dist q C + dist q C - workFnU C₀ σ ![r, C, C]))
        - workFnU C₀ σ ![r, p, q] + dist E B - workFnU C₀ σ ![r, E, B]
        ≤ lazyPot C₀ σ r)
    ∧ (∀ p q B B' C C' e e' : M,
        dist q C + dist q B = dist C B → dist q B' + dist q C' = dist B' C' →
      (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
        + (-dist r q + (dist q C + dist q C' - workFnU C₀ σ ![r, C, C']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ lazyPot C₀ σ r)
    ∧ (∀ p q B B' C' e e' : M, dist q B' + dist q C' = dist B' C' →
      (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
        + (-dist r q + (dist q B + dist q C' - workFnU C₀ σ ![r, B, C']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ lazyPot C₀ σ r)
    ∧ (∀ p q B B' E : M,
      (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
        + (-dist r q + (dist q B + dist q B' - workFnU C₀ σ ![r, B, B']))
        - workFnU C₀ σ ![r, p, q] + dist E B - workFnU C₀ σ ![r, E, B]
        ≤ lazyPot C₀ σ r) := by sorry

end KServer
