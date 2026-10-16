-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_coordinateRank_strict
-- name    : OAI.BoxTransport.Routing.coordinateRank_strict
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:15:46.635813+00:00
-- url     : https://prove2.me/theorems/9938d464-fb26-4100-8c2a-f7c909fda50f
-- title:
--   The lexicographic coordinate rank is strictly monotone in the key
-- statement:
--   Let $n\in\mathbb{N}$ and $f:\{0,\dots,n-1\}\to\mathbb{Q}$. Attach to every index $i$ the key $\kappa(i)=(f(i),i)\in\mathbb{Q}\times\mathbb{N}$, ordered lexicographically, and define the coordinate rank of $i$ as
--
--   $$\rho(i)=\#\{k\in\{0,\dots,n-1\}:\ \kappa(k)<\kappa(i)\}.$$
--
--   **Theorem.** For all indices $i,j$: if $\kappa(i)<\kappa(j)$, then $\rho(i)<\rho(j)$.
--
--   Thus $\rho(i)$ is the position of $i$ when the indices are sorted by the value $f(i)$, ties being broken by the index itself, and this position is strictly increasing in the key. In the box-routing construction the boxes are temporarily displaced along the first axis by an amount proportional to their rank with respect to the first coordinates of their centers; strict monotonicity of the rank makes these displacements respect the original order.
--
--   **Formalization Note** The key is `centerKey f i = toLex (f i, i.val)`, an element of the lexicographic product of $\mathbb{Q}$ and $\mathbb{N}$, and `coordinateRank f i` is the cardinality of the corresponding filtered `Finset` of indices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Motion.lean#L23-L35

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion

open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff

theorem OAI.BoxTransport.Routing.coordinateRank_strict {n : ℕ} {f : Fin n → ℚ} {i j : Fin n}
    (hij : centerKey f i < centerKey f j) : coordinateRank f i < coordinateRank f j := by sorry
