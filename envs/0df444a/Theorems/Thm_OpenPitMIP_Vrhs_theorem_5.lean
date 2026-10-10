-- Prove2me | Theorems.Thm_OpenPitMIP_Vrhs_theorem_5
-- name    : OpenPitMIP.Vrhs.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:19.139992+00:00
-- url     : https://prove2.me/theorems/e0c17ff0-612f-419b-8a07-a381d8fc4bd7
-- title:
--   Theorem 5, p. 1434 — simplified VRHS cut on MK: if q_b ≤ U then ∑_{b′∈rcl(b)} q_{b′} y^P_{b′} ≤ U x_b
-- statement:
--   Let $G=(\mathcal B,\mathcal A)$ be a directed acyclic graph on a finite set of blocks, $q\in\mathbb R^{\mathcal B}$ with $q_b>0$ for all $b$, and $U>0$. Let MK be the mode-knapsack set: the vectors $(x,y^P,y^W)$ with $\sum_b q_b y^P_b\le U$, $y^P_b+y^W_b=x_b$, $x_b\le 1$, $x_b>0\Rightarrow x_{b'}=1$ for every arc $(b,b')\in\mathcal A$, and $y^P,y^W\ge 0$. Write $b\prec b'$ when $\mathcal A$ contains a directed path from $b'$ to $b$, and $rcl(b)=\{b\}\cup\{b':b\prec b'\}$.
--
--   If $b\in\mathcal B$ satisfies $q_b\le U$, then every point of MK satisfies
--   $$\sum_{b'\in rcl(b)}q_{b'}\,y^P_{b'}\ \le\ U\,x_b.$$
--
--   This is the one-period, two-destination prototype of the VRHS production cuts: if a block's successors are sent to processing, the block itself must be extracted, and the right-hand side scales the capacity by its extraction level.
--
--   **Formalization Note** An arc $(b,b')$ is `A b b'` and means that extracting $b$ forces $b'$; $rcl(b)$ therefore collects $b$ and the blocks that can reach $b$ along arcs. The DAG, the positivity of $q$ and $U>0$ are the standing assumptions of MK (p. 1433).
-- source:
--   Oper. Res. 68(5), §5.2.1, Theorem 5, p. 1434

import Mathlib
import Definitions.Def_OpenPitMIP_Vrhs_Setting

namespace OpenPitMIP.Vrhs

/-- Theorem 5, Oper. Res. 68(5), p. 1434: in the mode-knapsack set MK over a DAG `G = (𝓑, 𝒜)` with
positive weights `q` and capacity `U > 0`, for every block `b` with `q_b ≤ U` the simplified VRHS
inequality `∑_{b' ∈ rcl(b)} q_{b'} y^P_{b'} ≤ U x_b` is valid. -/
theorem theorem_5 {B : Type} [Fintype B] (A : B → B → Prop) (hA : ∀ b, ¬ Relation.TransGen A b b)
    (q : B → ℝ) (hq : ∀ b, 0 < q b) (U : ℝ) (hU : 0 < U) (b : B) (hb : q b ≤ U) :
    ∀ v ∈ MK A q U, ∑ b' ∈ mkRcl A b, q b' * v.2.1 b' ≤ U * v.1 b := by sorry

end OpenPitMIP.Vrhs
