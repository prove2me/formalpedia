-- Prove2me | Theorems.Thm_OAI_TriangleFace198_expansion_image_eq
-- name    : OAI.TriangleFace198.expansion_image_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:48:31.36168+00:00
-- url     : https://prove2.me/theorems/de2a4fc2-d0a2-4932-83ac-851f580182bc
-- title:
--   Lifting the perfect matching polytope through a triangle expansion gives the tight triangle-cut slice
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$ (each edge has two distinct endpoints; parallel edges are allowed). A *perfect matching* of $G$ is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; its indicator vector is $\mathbf 1_M\in\mathbb{R}^E$. The *perfect matching polytope* of $G$ is
--   $$
--   \mathcal P(G)=\operatorname{conv}\{\mathbf 1_M:\ M\text{ a perfect matching of }G\}\subseteq\mathbb{R}^E .
--   $$
--
--   Fix a vertex $v\in V$ and a labelling $c:E\to\{0,1,2\}$ that is *local at $v$*: for each $i\in\{0,1,2\}$ there is exactly one edge $e_i$ incident to $v$ with $c(e_i)=i$. (Consequently $e_0,e_1,e_2$ are distinct and are all the edges incident to $v$.) The *triangle expansion* $H$ of $G$ at $v$ along $c$ has vertex set $V\sqcup\{t_1,t_2\}$, where we put $t_0=v$, and edge set $E\sqcup\{n_0,n_1,n_2\}$: an old edge $e$ keeps its endpoints, except that an endpoint equal to $v$ is moved to $t_{c(e)}$, and the new edge $n_i$ joins $t_{i+1}$ and $t_{i+2}$ (indices modulo $3$). Let $T=\{t_0,t_1,t_2\}$ and, for $y\in\mathbb{R}^{E\sqcup\{n_0,n_1,n_2\}}$, let $y(\delta_H(T))$ denote the sum of $y_g$ over all edges $g$ of $H$ with exactly one endpoint in $T$. Finally let $\Phi:\mathbb{R}^E\to\mathbb{R}^{E\sqcup\{n_0,n_1,n_2\}}$ be the linear lift
--   $$
--   \Phi(x)_e=x_e\quad(e\in E),\qquad \Phi(x)_{n_i}=x_{e_i}\quad(i=0,1,2).
--   $$
--
--   **Theorem.** The lift maps the perfect matching polytope of $G$ exactly onto the part of the perfect matching polytope of $H$ where the cut around the triangle has weight one:
--   $$
--   \Phi\big(\mathcal P(G)\big)=\big\{\,y\in\mathcal P(H):\ y(\delta_H(T))=1\,\big\}.
--   $$
--
--   The theorem identifies $\mathcal P(G)$, via the injective linear map $\Phi$, with the slice of $\mathcal P(H)$ on which the odd cut around the new triangle is tight. Since this slice is a face of $\mathcal P(H)$ (a companion result), questions about the facial structure of $\mathcal P(G)$, such as minimal faces through a given point, can be transferred to $\mathcal P(H)$ and back.
--
--   **Formalization Note** The local-labelling hypothesis is `LocalLabels G v c`; the edge $e_i$ is `localEdge G c v hc i`, selected by choice from the uniqueness statement; $\Phi$ is the linear map `localExtension G c v hc`; $H$ is `triangleExpansion G c v`, whose tips $t_0,t_1,t_2$ are `Sum.inl v`, `Sum.inr 0`, `Sum.inr 1`; $T$ is `triangleVertices v`; and $y(\delta_H(T))$ is `cutMass y (triangleVertices v)`. The polytope is `convexHull ℝ (Set.range G.indicator)`. No perfect matching of $G$ is assumed; if $G$ has none, the statement says that the slice on the right is empty as well.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TriangleFace/MatchingImage.lean#L48-L66

import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Entropy
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Duality
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_EdgeReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_MinimalFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_FractionalReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Components
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_TriangleExpansion

open OAI OAI.TriangleFace198
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

theorem OAI.TriangleFace198.expansion_image_eq (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) :
    localExtension G c v hc '' G.polytope =
      {y | y ∈ (triangleExpansion G c v).polytope ∧
        (triangleExpansion G c v).cutMass y (triangleVertices v) = 1} := by sorry
