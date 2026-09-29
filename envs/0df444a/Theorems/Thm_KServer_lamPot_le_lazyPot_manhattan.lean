-- Prove2me | Theorems.Thm_KServer_lamPot_le_lazyPot_manhattan
-- name    : KServer.lamPot_le_lazyPot_manhattan
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T18:16:29.387391+00:00
-- url     : https://prove2.me/theorems/51773092-eb23-40c1-ba20-2cfd8b1f1135
-- title:
--   The first auxiliary potential is redundant in the city-block plane
-- statement:
--   Let $w$ be a work function for three servers with last request $r$ in the **city-block plane** $\mathbb{R}^2_1$. Then the first auxiliary potential is redundant:
--
--   $$\Lambda_{w,r} \;\le\; \Psi_{w,r}.$$
--
--   ## Role
--
--   This is one of the two geometric lemmas on which the $3$-competitiveness of the Work Function Algorithm in the Manhattan plane rests. The general theory reduces that competitiveness to the single inequality $\hat\Psi_{w,r} = \max\{\Psi_{w,r}, \Lambda_{w,r}, \Gamma_{w,r}\} \le \Psi_{w,r}$, that is, to the redundancy of the two auxiliary potentials that the twelve-case analysis of the update property forced one to introduce. The present statement disposes of $\Lambda$; the companion statement disposes of $\Gamma$.
--
--   The argument has two halves. The first is geometric and is where the plane is used: every finite set of points sits inside an axis-parallel rectangle, every point of which lies on **both** diagonals, and any two points of which are completed to a geodesic by some corner. Because of this, each of the six free points $b, b', c, c', e, e'$ in an instance of $\Lambda_{w,r}$ may be pushed out to a corner — the Lipschitz property of the work function pays for the detour — and the pair $e, e'$ may be pushed further onto a diagonal. What is left is a finite comparison, over the four corners, between an instance of $\Lambda_{w,r}$ and an instance of $\Psi_{w,r}$.
--
--   The second half is that finite comparison, and it is not geometric at all: each configuration of corners is settled by the triangle inequality, the Lipschitz property and quasiconvexity, in a form valid in any metric space. The relations the rectangle supplies — "$q$ lies on a geodesic between $c$ and $b$", "$b$ and $b'$ coincide", and so on — are exactly the hypotheses of the seven configuration lemmas that were established separately.
--
--   **Formalization note.** The reduction to a pointwise statement about free witnesses is an $\varepsilon$-argument, since suprema over a metric space need not be attained. The corner analysis is carried out over all $4^5$ assignments of the four corners to $b, b', c, c'$ together with the four choices of diagonal for $e, e'$; every one of them is closed by one of the seven configuration lemmas, applied after at most a few of the symmetries of $\Lambda$ (interchanging $b$ with $b'$, $c$ with $c'$, $e$ with $e'$, or the two triples with each other), each of which is an identity proved from the permutation invariance of the work function.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Lemma 5: 'Let w be a work function with last request r in the Manhattan plane. Then Lambda_{w,r} <= Psi_{w,r}.'

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem lamPot_le_lazyPot_manhattan (C₀ : Config 3 (PiLp 1 fun _ : Fin 2 => ℝ))
    (σ : List (PiLp 1 fun _ : Fin 2 => ℝ)) (r : PiLp 1 fun _ : Fin 2 => ℝ) :
    lamPot C₀ σ r ≤ lazyPot C₀ σ r := by sorry

end KServer
