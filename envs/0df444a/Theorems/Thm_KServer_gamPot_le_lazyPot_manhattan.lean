-- Prove2me | Theorems.Thm_KServer_gamPot_le_lazyPot_manhattan
-- name    : KServer.gamPot_le_lazyPot_manhattan
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T18:52:52.196414+00:00
-- url     : https://prove2.me/theorems/ab60becb-10a1-4091-8bea-980fbc1aebb0
-- title:
--   The second auxiliary potential is redundant in the city-block plane
-- statement:
--   Let $w$ be a work function for three servers with last request $r$ in the **city-block plane** $\mathbb{R}^2_1$. Then the second auxiliary potential is redundant:
--
--   $$\Gamma_{w,r} \;\le\; \Psi_{w,r}.$$
--
--   ## Role
--
--   Together with the companion statement for $\Lambda$, this completes the verification that
--   $$\hat\Psi_{w,r} = \max\{\Psi_{w,r},\, \Lambda_{w,r},\, \Gamma_{w,r}\} \;\le\; \Psi_{w,r}$$
--   in the Manhattan plane — the single hypothesis under which the Work Function Algorithm for three servers is $3$-competitive. The two auxiliary potentials were forced into existence by two of the twelve cases in the analysis of the update property; this pair of lemmas shows that in this particular plane they never actually bind.
--
--   The argument follows the same plan as for $\Lambda$. Every finite set of points sits inside an axis-parallel rectangle, every point of which lies on both diagonals, and any two points of which are completed to a geodesic by some corner; so each of the free points $b, b', f, d, d'$ in an instance of $\Gamma_{w,r}$ may be pushed out to a corner, and the pair $d, d'$ pushed further onto a diagonal. What remains is a finite comparison over the corners, and that comparison is not geometric: it is settled by the triangle inequality, the Lipschitz property and quasiconvexity, in forms valid in any metric space.
--
--   One feature is specific to $\Gamma$: the last request $r$ must itself be taken inside the rectangle. It is needed in the case where $b$ and $b'$ land in opposite corners, where the sum $pb + pb'$ collapses to the diagonal $bb'$ and the bound has to reconstitute that diagonal as $rb + rb'$.
--
--   **Formalization note.** The reduction to a pointwise statement about free witnesses is an $\varepsilon$-argument, since suprema over a metric space need not be attained; $\Gamma$ has only one inner two-point shadow, so two extractions suffice. The push for the group $dd' - w(q,d) - w(q,d')$ has a different shape from the one used for $\Lambda$ — the two work-function values share the point $q$ rather than each other — and is derived directly from the Lipschitz property.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Lemma 6: 'Let w be a work function with last request r in the Manhattan plane. Then Gamma_{w,r} <= Psi_{w,r}.'

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem gamPot_le_lazyPot_manhattan (C₀ : Config 3 (PiLp 1 fun _ : Fin 2 => ℝ))
    (σ : List (PiLp 1 fun _ : Fin 2 => ℝ)) (r : PiLp 1 fun _ : Fin 2 => ℝ) :
    gamPot C₀ σ r ≤ lazyPot C₀ σ r := by sorry

end KServer
