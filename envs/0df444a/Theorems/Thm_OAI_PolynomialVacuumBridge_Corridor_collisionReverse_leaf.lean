-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_collisionReverse_leaf
-- name    : OAI.PolynomialVacuumBridge.Corridor.collisionReverse_leaf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:54:56.600975+00:00
-- url     : https://prove2.me/theorems/837d6755-c127-4a01-9716-861470e51dc1
-- title:
--   Collision reversal is an involution on colliding walks
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. Let $D$ be a finite domain, $g$ a germ whose previous vertex is outside $D$, and $w$ a stopped walk from $g$ in $D$ that ends at a vertex of $D$, i.e. it ends by colliding with its own past. Then the collision reversal $w'$ (reverse the loop closed at the collision vertex) satisfies
--   $$
--   w'\in\mathrm{leaves}(D,g),\quad\mathrm{end}(w')\in D,\quad\{\text{vertices of }w'\}=\{\text{vertices of }w\},\quad(w')'=w .
--   $$
--
--   Colliding walks thus come in pairs with the same vertex set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/CollisionHistories.lean#L213-L230

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

theorem OAI.PolynomialVacuumBridge.Corridor.collisionReverse_leaf (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hw : w ∈ leaves D g) (hg : (reverseGerm g).1 ∉ D)
    (ht : (terminalGerm g w).1 ∈ D) :
    collisionReverse g w ∈ leaves D g ∧
    (terminalGerm g (collisionReverse g w)).1 ∈ D ∧
    (∀ v, v ∈ traced g (collisionReverse g w) ↔ v ∈ traced g w) ∧
    collisionReverse g (collisionReverse g w) = w := by sorry
