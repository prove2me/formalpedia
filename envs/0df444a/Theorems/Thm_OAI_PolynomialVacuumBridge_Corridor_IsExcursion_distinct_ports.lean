-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_IsExcursion_distinct_ports
-- name    : OAI.PolynomialVacuumBridge.Corridor.IsExcursion.distinct_ports
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:45:41.922197+00:00
-- url     : https://prove2.me/theorems/1e244196-279d-41be-8769-51d6d3c14af4
-- title:
--   An excursion does not exit through its entrance port
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. An excursion of a finite domain $D$ is a pair $(g,w)$ where $g$ enters $D$ from outside, $w$ is a self-avoiding walk from $g$ stopped in $D$, and the walk ends outside $D$. Its exit port is $\mathrm{reverseGerm}(\mathrm{terminalGerm}(g,w))$, the germ of the last edge traversed backwards. Then
--   $$
--   \mathrm{reverseGerm}\bigl(\mathrm{terminalGerm}(g,w)\bigr)\ne g .
--   $$
--
--   So an excursion never leaves $D$ through the same edge by which it entered.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Excursions.lean#L399-L416

import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.IsExcursion.distinct_ports {D : Finset Vertex} {e : Germ × List Bool}
    (he : IsExcursion D e) : reverseGerm (terminalGerm e.1 e.2) ≠ e.1 := by sorry
