-- Prove2me | Theorems.Thm_OAI_Paper256_interior_line_pair
-- name    : OAI.Paper256.interior_line_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:04:35.180983+00:00
-- url     : https://prove2.me/theorems/f7569765-5848-4203-b090-e178ae96aeff
-- title:
--   An interior point admits a symmetric segment in every direction
-- statement:
--   Let $V$ be a real normed vector space, $K\subseteq V$ an arbitrary subset, and $e$ a point in the interior of $K$. Then for every direction $x\in V$ there is $\varepsilon>0$ such that both points at distance $\varepsilon$ along $\pm x$ from $e$ lie in $K$:
--   $$\exists\,\varepsilon>0:\qquad e+\varepsilon x\in K\quad\text{and}\quad e-\varepsilon x\in K .$$
--
--   This elementary fact is used repeatedly with $K$ the open set of positive definite matrices: from a positive definite matrix one can move a little in any symmetric direction $\pm H$ and stay positive definite. It underlies, for instance, the statement that for a positive linear map $D$ the kernel of $D(I)$ is contained in the kernel of every $D(X)$, and the argument that certain matrices in a spectrahedral representation cannot be positive definite.
--
--   **Formalization Note** No convexity of $K$ is assumed; only the topology of the normed space $V$ is used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PencilKernel.lean#L27-L41

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation

open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder
universe u

theorem OAI.Paper256.interior_line_pair {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} {e : V} (he : e ∈ interior K) (x : V) :
    ∃ ε : ℝ, 0 < ε ∧ e + ε • x ∈ K ∧ e - ε • x ∈ K := by sorry
