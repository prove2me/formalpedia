-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_collision_root_slots
-- name    : OAI.PolynomialVacuumBridge.Corridor.collision_root_slots
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:54:18.352111+00:00
-- url     : https://prove2.me/theorems/36d13f7d-0566-449c-bb6f-b8695fd73f2e
-- title:
--   A walk returning to its start re-enters through the unused slot
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. Let $b::w$ be a walk from $g$ with duplicate-free trace that ends at the starting vertex $g_1$, and suppose it never visits the vertex behind $g$ (the vertex $\mathrm{reverseGerm}(g)_1$). Let $g'$ be its terminal germ. Then
--   $$
--   \mathrm{stem}(g',\bar b)=g\qquad\text{and}\qquad\mathrm{advance}(g',\bar b)=\mathrm{advance}(g,b).
--   $$
--
--   So the walk arrives back through the third slot at $g_1$, and switching the last turn re-enters the original first step.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/CollisionHistories.lean#L67-L86

import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.collision_root_slots (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g (b :: w)) :
    stemGerm (terminalGerm g (b :: w)) (!b) = g ∧
    advance (terminalGerm g (b :: w)) (!b) = advance g b := by sorry
