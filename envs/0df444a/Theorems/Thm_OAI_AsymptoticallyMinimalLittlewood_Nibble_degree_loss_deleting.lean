-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_degree_loss_deleting
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.degree_loss_deleting
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:16:08.575042+00:00
-- url     : https://prove2.me/theorems/a7735652-3458-4ec0-b440-a7a56692410c
-- title:
--   Deleting a vertex set lowers a degree by at most its size times the codegree bound
-- statement:
--   Let $V$ be a set of vertices and $E$ a set of edge labels. A hypergraph is given by a finite set $S\subseteq E$ of edges together with a finite vertex set $A_e\subseteq V$ for every label $e$. For a vertex $v$ let $S(v)=\{e\in S: v\in A_e\}$ and $\deg_S(v)=|S(v)|$; for a vertex set $X$ let $S_X=\{e\in S: A_e\subseteq X\}$ be the set of edges lying entirely inside $X$, so that $\deg_{S_X}(v)=|\{e\in S(v): A_e\subseteq X\}|$.
--
--   Let $U,B\subseteq V$ be finite vertex sets and $C\ge0$, and assume that every edge of $S$ lies inside $U$, i.e. $A_e\subseteq U$ for $e\in S$. Let $v$ be a vertex with $v\notin B$ whose codegree with every vertex of $B$ is at most $C$: $|S(v)\cap S(w)|\le C$ for all $w\in B$ with $w\ne v$. Then
--
--   $$
--   \deg_S(v)-|B|\,C\le\deg_{S_{U\setminus B}}(v).
--   $$
--
--   In words, deleting the vertices of $B$ (together with all edges meeting $B$) lowers the degree of any other vertex by at most $|B|\,C$. In a round of the nibble method a small set of vertices with atypical behaviour is discarded, and this bound shows that the surviving vertices keep almost all of their degree when codegrees are small.
--
--   **Formalization Note** $S(v)$ is `incident S A v` and $S_X$ is `restrictEdges S A X`. The vertex $v$ is not required to lie in $U$, and the condition $w\ne v$ in the hypothesis is automatic because $v\notin B$. The hypothesis $C\ge0$ is part of the statement but is not needed in the proof, and the type of edge labels need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Nibble.lean#L268-L299

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
universe uI uE uV
open scoped BigOperators
open Finset
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype E] in
theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.degree_loss_deleting (U B : Finset V) (S : Finset E) (A : E → Finset V)
    {C : ℝ} (_hC : 0 ≤ C) (hsub : ∀ e ∈ S, A e ⊆ U)
    (v : V) (hc : ∀ w ∈ B, v ≠ w → ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (hv : v ∉ B) :
    ((incident S A v).card : ℝ) - B.card*C ≤
      ((incident (restrictEdges S A (U \ B)) A v).card : ℝ) := by sorry
