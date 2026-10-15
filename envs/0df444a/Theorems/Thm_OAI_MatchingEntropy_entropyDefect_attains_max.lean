-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_entropyDefect_attains_max
-- name    : OAI.MatchingEntropy.entropyDefect_attains_max
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:20:36.139+00:00
-- url     : https://prove2.me/theorems/b498838e-0537-41d8-b613-e36b53402344
-- title:
--   The entropy defect attains its maximum on the perfect matching polytope
-- statement:
--   Let $G$ be a finite loopless multigraph with vertex set $V$ and edge set $E$: every edge $e\in E$ has two distinct endpoints, and parallel edges are allowed (they are distinct elements of $E$). Assume that $|V|$ is even and that $G$ has at least one perfect matching, and let $m$ be a real number. A perfect matching of $G$ is a set $M\subseteq E$ such that every vertex is an endpoint of exactly one edge of $M$; write $\mathcal{M}(G)$ for the finite set of perfect matchings and $\mathbf{1}_M\in\{0,1\}^E$ for the indicator vector of $M$. The perfect matching polytope $P(G)$ is the convex hull of the vectors $\mathbf{1}_M$. For $y\in\mathbb{R}^E$, a feasible law for $y$ is a probability vector $p=(p_M)_{M\in\mathcal{M}(G)}$ with mean $\sum_M p_M\mathbf{1}_M=y$; let $\Pi(G,y)$ be the set of feasible laws, so that $y\in P(G)$ exactly when $\Pi(G,y)$ is nonempty. With the Shannon entropy $H(p)=-\sum_M p_M\log p_M$ (with $0\log 0=0$), the maximum matching entropy at $y$ is
--
--   $$
--   H^*(G,y)=\sup\{H(p):\ p\in\Pi(G,y)\}.
--   $$
--
--   For $y\in\mathbb{R}^E$ let $H(y)=-\sum_{e\in E}y_e\log y_e$ be the entropy of the edge vector itself (not normalized), and for a real parameter $m$ define the entropy defect
--
--   $$
--   D_m(y)=H(y)-8m\bigl(1-e^{-H(y)/m}\bigr)-H^*(G,y).
--   $$
--
--   **Theorem.** $D_m$ attains its maximum on $P(G)$: there is $x\in P(G)$ such that
--
--   $$
--   D_m(y)\le D_m(x)\qquad\text{for all } y\in P(G).
--   $$
--
--   When $|V|=2m$, the entropy comparison $H(y)-H^*(G,y)\le 8m\bigl(1-e^{-H(y)/m}\bigr)$ says precisely that $D_m\le 0$ on $P(G)$. It is proved by contradiction at a maximizer of $D_m$, where first- and second-order optimality conditions are available; this theorem supplies such a maximizer.
--
--   **Formalization Note** $D_m$ is `entropyDefect G m`, i.e. `entropyBarrier m (entropy y) - maxMatchingEntropy G y` with the barrier $B_m(h)=h-8m(1-e^{-h/m})$. The parameter $m$ is an arbitrary real number; for $m=0$ Lean's convention $h/0=0$ gives $B_0(h)=h$. Entropies use $0\log 0=0$, and the supremum defining $H^*$ is an `sSup`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Continuity.lean#L62-L77

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

theorem OAI.MatchingEntropy.entropyDefect_attains_max (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) (hPM : Nonempty G.Matching) (m : ℝ) :
    ∃ x ∈ G.polytope, ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x := by sorry
