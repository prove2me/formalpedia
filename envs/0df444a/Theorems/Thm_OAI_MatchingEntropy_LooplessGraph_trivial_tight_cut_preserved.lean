-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_trivial_tight_cut_preserved
-- name    : OAI.MatchingEntropy.LooplessGraph.trivial_tight_cut_preserved
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:15:23.048751+00:00
-- url     : https://prove2.me/theorems/e9e452b5-2451-4ad9-acf5-e26f91fd55b0
-- title:
--   Without nontrivial tight odd cuts, degree-balanced directions vanish on every tight odd cut
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$: every edge has two distinct endpoints, and parallel edges are allowed and kept distinct. For $x\in\mathbb R^E$ and $v\in V$ let $d_x(v)=\sum_{e\ni v}x_e$ be the weighted degree of $v$ (the sum over the edges incident to $v$). For $S\subseteq V$ let $\delta(S)$ be the set of edges with exactly one endpoint in $S$, and $x(\delta(S))=\sum_{e\in\delta(S)}x_e$. A set $S\subseteq V$ is *tight* for $x$ if $x(\delta(S))=1$, and an odd set $S$ is *nontrivial* if $|S|\ge3$ and $|V\setminus S|\ge3$.
--
--   Assume that $|V|$ is even, and let $x\in\mathbb R^E$ have no nontrivial tight odd set: there is no $S\subseteq V$ with $|S|$ odd, $|S|\ge3$, $|V\setminus S|\ge3$ and $x(\delta(S))=1$. Let $u\in\mathbb R^E$ satisfy $d_u(v)=0$ for every vertex $v$. Then
--
--   $$
--   x(\delta(S))=1\ \Longrightarrow\ u(\delta(S))=0\qquad\text{for every } S\subseteq V \text{ with } |S| \text{ odd}.
--   $$
--
--   In other words, once all tight odd cuts are trivial, only the degree equations constrain a direction of motion: the remaining tight odd cuts are the cuts of single vertices or of complements of single vertices, and they are controlled by the degrees. This settles the base case of the inductions over tight odd cuts, both in the proof of Edmonds' perfect matching polytope theorem and in the face-codimension bound, where it shows that the face codimension is at most $|V|$.
--
--   **Formalization Note** No membership of $x$ in the degree and odd-cut polytope is assumed. The complement $V\setminus S$ is `Sᶜ` in the finite vertex type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Polytope.lean#L304-L323

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

open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem OAI.MatchingEntropy.LooplessGraph.trivial_tight_cut_preserved (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1)
    (u : E → ℝ) (hdeg : ∀ v, G.degree u v=0) :
    ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0 := by sorry
