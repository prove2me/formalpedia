-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_normalized_face_mem
-- name    : OAI.MatchingEntropy.normalized_face_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:25:12.049832+00:00
-- url     : https://prove2.me/theorems/4918d9d7-8714-4d31-9a96-ebe378576f58
-- title:
--   Normalized face directions lie in the span of the optimizer's normalized matching vectors
-- statement:
--   Let $G$ be a finite loopless multigraph with vertex set $V$ and edge set $E$: every edge $e\in E$ has two distinct endpoints, and parallel edges are allowed (they are distinct elements of $E$). Assume that $|V|$ is even. A perfect matching of $G$ is a set $M\subseteq E$ such that every vertex is an endpoint of exactly one edge of $M$; write $\mathcal{M}(G)$ for the finite set of perfect matchings and $\mathbf{1}_M\in\{0,1\}^E$ for the indicator vector of $M$. The perfect matching polytope $P(G)$ is the convex hull of the vectors $\mathbf{1}_M$. For $y\in\mathbb{R}^E$, a feasible law for $y$ is a probability vector $p=(p_M)_{M\in\mathcal{M}(G)}$ with mean $\sum_M p_M\mathbf{1}_M=y$; let $\Pi(G,y)$ be the set of feasible laws, so that $y\in P(G)$ exactly when $\Pi(G,y)$ is nonempty. With the Shannon entropy $H(p)=-\sum_M p_M\log p_M$ (with $0\log 0=0$), the maximum matching entropy at $y$ is
--
--   $$
--   H^*(G,y)=\sup\{H(p):\ p\in\Pi(G,y)\}.
--   $$ For $z\in\mathbb{R}^E$, a vertex $v$ and a set $T\subseteq V$ write $\deg_z(v)=\sum_{e\ni v}z_e$ and $z(\delta(T))=\sum_{e\in\delta(T)}z_e$, where $\delta(T)$ is the set of edges with exactly one endpoint in $T$.
--
--   Let $x\in\mathbb{R}^E$ and let $p\in\Pi(G,x)$ be an entropy maximizer, $H(p)=H^*(G,x)$. Let $E_+=\{e\in E: x_e>0\}$ be the positive support of $x$, and for $u\in\mathbb{R}^{E_+}$ let $\tilde u\in\mathbb{R}^E$ be its extension by zero. The active face space of $x$ is the linear subspace
--
--   $$
--   \mathcal{F}(G,x)=\Bigl\{u\in\mathbb{R}^{E_+}:\ \deg_{\tilde u}(v)=0\ \text{for all } v\in V,\ \ \tilde u(\delta(T))=0\ \text{for every odd } T\subseteq V \text{ with } x(\delta(T))=1\Bigr\},
--   $$
--
--   the directions supported on $E_+$ that preserve all vertex degrees and the masses of all odd cuts that are tight at $x$.
--
--   For each perfect matching $M$ let $b_M\in\mathbb{R}^{E_+}$ be the normalized centred vector $b_M(e)=(\mathbf{1}_M(e)-x_e)/\sqrt{x_e}$, and let $\mathcal{W}_p=\operatorname{span}\{b_M:\ M\in\mathcal{M}(G),\ p_M>0\}\subseteq\mathbb{R}^{E_+}$.
--
--   **Theorem.** For every $u\in\mathcal{F}(G,x)$,
--
--   $$
--   \Bigl(\frac{u_e}{\sqrt{x_e}}\Bigr)_{e\in E_+}\in\mathcal{W}_p .
--   $$
--
--   Thus $u\mapsto u/\sqrt{x}$ is an injective linear map from the active face space into the span of the normalized matching vectors charged by the optimizer, and $\dim\mathcal{F}(G,x)\le\dim\mathcal{W}_p$. Since $\mathcal{W}_p$ is the column space of the normalized matching covariance, this is the bridge from the polyhedral face structure at $x$ to the rank of that covariance. No assumption on the dimension or support of the face is made.
--
--   **Formalization Note** The vector $b_M$ is `matchingNormalized G x M` and $\mathcal{W}_p$ is `weightedDirectionSpace p (matchingNormalized G x)`. Evenness of $|V|$ is used through Edmonds' theorem.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/MatchingCovariance.lean#L59-L98

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
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Covariance
import Definitions.Def_OAI_Combinatorics_PerfectMatching_MatchingCovariance

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
open Matrix
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem OAI.MatchingEntropy.normalized_face_mem (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x)
    {u : {e // 0 < x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    (fun e => u e/Real.sqrt (x e.val)) ∈ weightedDirectionSpace p (matchingNormalized G x) := by sorry
