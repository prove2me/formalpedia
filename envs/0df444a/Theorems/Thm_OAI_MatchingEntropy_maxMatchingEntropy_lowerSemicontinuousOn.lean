-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_maxMatchingEntropy_lowerSemicontinuousOn
-- name    : OAI.MatchingEntropy.maxMatchingEntropy_lowerSemicontinuousOn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:19:59.256496+00:00
-- url     : https://prove2.me/theorems/201b1653-8612-40f3-9b9f-e3d15d85823a
-- title:
--   Maximum matching entropy is lower semicontinuous on the perfect matching polytope
-- statement:
--   Let $G$ be a finite loopless multigraph with vertex set $V$ and edge set $E$: every edge $e\in E$ has two distinct endpoints, and parallel edges are allowed (they are distinct elements of $E$). Assume that $|V|$ is even. A perfect matching of $G$ is a set $M\subseteq E$ such that every vertex is an endpoint of exactly one edge of $M$; write $\mathcal{M}(G)$ for the finite set of perfect matchings and $\mathbf{1}_M\in\{0,1\}^E$ for the indicator vector of $M$. The perfect matching polytope $P(G)$ is the convex hull of the vectors $\mathbf{1}_M$. For $y\in\mathbb{R}^E$, a feasible law for $y$ is a probability vector $p=(p_M)_{M\in\mathcal{M}(G)}$ with mean $\sum_M p_M\mathbf{1}_M=y$; let $\Pi(G,y)$ be the set of feasible laws, so that $y\in P(G)$ exactly when $\Pi(G,y)$ is nonempty. With the Shannon entropy $H(p)=-\sum_M p_M\log p_M$ (with $0\log 0=0$), the maximum matching entropy at $y$ is
--
--   $$
--   H^*(G,y)=\sup\{H(p):\ p\in\Pi(G,y)\}.
--   $$
--
--   **Theorem.** The function $y\mapsto H^*(G,y)$ is lower semicontinuous on $P(G)$, relative to $P(G)$: for every $x\in P(G)$ and every real $r<H^*(G,x)$ there is a neighbourhood $U$ of $x$ such that $r<H^*(G,y)$ for all $y\in P(G)\cap U$. Equivalently,
--
--   $$
--   \liminf_{y\to x,\ y\in P(G)}H^*(G,y)\ \ge\ H^*(G,x)\qquad\text{for every } x\in P(G).
--   $$
--
--   Since $H^*(G,y)$ is the value of an optimization problem over laws with prescribed edge marginals, its regularity in $y$ is not automatic, and lower semicontinuity is exactly what is needed. Together with the continuity of $y\mapsto -\sum_e y_e\log y_e$, this theorem makes the entropy defect upper semicontinuous on the compact set $P(G)$, which guarantees that the defect attains its maximum.
--
--   **Formalization Note** $H^*(G,\cdot)$ is `maxMatchingEntropy G`, defined as an `sSup` of `entropy` over `G.feasibleLaws y`, with entropy built from `Real.negMulLog`. For $y\notin P(G)$ the set is empty and Lean's convention gives the value $0$, but such points play no role because semicontinuity is relative to $P(G)$ (`LowerSemicontinuousOn`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Continuity.lean#L37-L60

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem OAI.MatchingEntropy.maxMatchingEntropy_lowerSemicontinuousOn (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) :
    LowerSemicontinuousOn (maxMatchingEntropy G) G.polytope := by sorry
