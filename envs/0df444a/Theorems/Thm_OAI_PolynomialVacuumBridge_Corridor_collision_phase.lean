-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_collision_phase
-- name    : OAI.PolynomialVacuumBridge.Corridor.collision_phase
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:53:40.059072+00:00
-- url     : https://prove2.me/theorems/5fea902a-42e1-46b7-9906-9b84492a6808
-- title:
--   Phase cancellation when a walk closes a loop
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. Let $b::w$ be a simple closed walk from $g$ whose flow is represented by a potential $p$ with values in $\{0,\varepsilon\}$, $\varepsilon=\pm1$, $p\ne0$. Let $F$ be the face next to the unused slot of $(g,b)$. Then
--   $$
--   \mathrm{wordWeight}(\bar b::w)+\mathrm{wordWeight}(b::\mathrm{reverseTurns}\,w)=\begin{cases}0,&p(F)=0,\\-2\lambda^{|w|+1},&p(F)\ne0.\end{cases}
--   $$
--
--   This is the local cancellation behind the parafermionic observable at the critical activity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/CollisionPhase.lean#L99-L128

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

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.collision_phase : CollisionPhase := by sorry
