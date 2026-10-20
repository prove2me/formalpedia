-- Prove2me | Theorems.Thm_OAI_TriangleFace198_expansion_image_extreme
-- name    : OAI.TriangleFace198.expansion_image_extreme
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:51:25.093259+00:00
-- url     : https://prove2.me/theorems/9526e546-3cbe-46a7-b81e-61b7ead7d77f
-- title:
--   The lifted perfect matching polytope is a face of the triangle expansion's matching polytope
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
--   **Theorem.** The lifted polytope $\Phi(\mathcal P(G))$ is an extreme subset (a face) of $\mathcal P(H)$: it is contained in $\mathcal P(H)$, and for all $y,z\in\mathcal P(H)$ and $0<\lambda<1$,
--   $$
--   \lambda y+(1-\lambda)z\in\Phi\big(\mathcal P(G)\big)\quad\Longrightarrow\quad y\in\Phi\big(\mathcal P(G)\big)\ \text{ and }\ z\in\Phi\big(\mathcal P(G)\big).
--   $$
--
--   Together with the injectivity of $\Phi$, this makes $\Phi$ an affine embedding of $\mathcal P(G)$ onto a face of $\mathcal P(H)$. That is exactly the hypothesis under which minimal faces are transported: the smallest face of $\mathcal P(H)$ through $\Phi(x)$ is the image of the smallest face of $\mathcal P(G)$ through $x$. Convexity of $\Phi(\mathcal P(G))$, also needed for that purpose, holds because it is a linear image of a convex set; it is not part of this statement.
--
--   **Formalization Note** The statement is Mathlib's `IsExtreme ℝ (triangleExpansion G c v).polytope (localExtension G c v hc '' G.polytope)`. Mathlib's definition only asks that the first endpoint $y$ lie in the subset, which is equivalent to the two-endpoint formulation above because open segments are symmetric. The hypothesis `hc : LocalLabels G v c` is the local-labelling condition, and $\Phi$ is `localExtension G c v hc`. No perfect matching of $G$ is assumed (if there is none, the subset is empty and trivially extreme).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TriangleFace/MatchingImage.lean#L68-L84

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

theorem OAI.TriangleFace198.expansion_image_extreme (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) :
    IsExtreme ℝ (triangleExpansion G c v).polytope (localExtension G c v hc '' G.polytope) := by sorry
