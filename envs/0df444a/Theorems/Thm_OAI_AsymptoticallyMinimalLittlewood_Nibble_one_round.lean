-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_one_round
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.one_round
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:19:24.347238+00:00
-- url     : https://prove2.me/theorems/64d0377c-4131-486a-a8c1-2fa6f6f9e863
-- title:
--   One nibble round: a partial matching leaving a smaller almost regular hypergraph
-- statement:
--   Let $V$ be a set of vertices and $E$ a finite set of edge labels. A hypergraph is given by a finite set $S\subseteq E$ of edges together with a finite vertex set $A_e\subseteq V$ for every label $e$. For a vertex $v$ let $S(v)=\{e\in S: v\in A_e\}$ be the set of edges containing $v$ and $\deg_S(v)=|S(v)|$ its degree; for vertices $v\ne w$ the number $|S(v)\cap S(w)|$ is their codegree. For a set $T$ of edges write $\deg_T(v)=|\{e\in T: v\in A_e\}|$, and for a set $M$ of edges write $\bigcup_{e\in M}A_e$ for the set of vertices it covers.
--
--   Let $U\subseteq V$ be finite and let $r\ge1$ be an integer. Let $D,\varepsilon,C,a,K$ be real numbers with $D\ge1$, $0\le\varepsilon\le D/4$, $C\ge0$, $0<a\le1/16$, $ra\le1/4$, $K\ge0$, and
--   $|U|\,C\le KD$, $C\le aD$, $512\,r\le a\,|U|$, $16\,r^2(K+1)^2\le a^5|U|$.
--   Assume that the hypergraph is $r$-uniform on $U$ ($A_e\subseteq U$ and $|A_e|=r$ for all $e\in S$), almost $D$-regular ($|\deg_S(v)-D|\le\varepsilon$ for all $v\in U$), and has codegrees at most $C$ ($|S(v)\cap S(w)|\le C$ for all distinct $v,w\in U$).
--
--   Then there are a vertex set $W\subseteq U$ and edge sets $T\subseteq S$ and $M\subseteq S$ such that
--
--   1. every edge of $T$ lies inside $W$: $A_e\subseteq W$ for all $e\in T$;
--   2. $M$ is a matching: $A_e\cap A_f=\emptyset$ for all distinct $e,f\in M$;
--   3. $W$ is disjoint from the vertices covered by $M$: $W\cap\bigcup_{e\in M}A_e=\emptyset$;
--   4. $|W|\le(1-a/2)\,|U|$;
--   5. few vertices are wasted: $\big|U\setminus\big(W\cup\bigcup_{e\in M}A_e\big)\big|\le(16r+1)\,a^2\,|U|$;
--   6. the residual hypergraph $(W,T)$ is again almost regular: for every $v\in W$,
--
--   $$
--   \Big|\deg_T(v)-\big(1-(r-1)a\big)D\Big|\le(1+2ra)\,\varepsilon+8r^2a^2D.
--   $$
--
--   This is one step of the semi-random "nibble" method for packing: the matching $M$ is set aside, the active vertex set shrinks by the factor $1-a/2$, and the remaining hypergraph $(W,T)$ is again $r$-uniform, almost regular with degree about $(1-(r-1)a)D$, and has codegrees at most $C$ (it is a sub-hypergraph), while at most $(16r+1)a^2|U|$ vertices are neither kept active nor covered by $M$. Iterating it is the basis of an almost-perfect-matching theorem for almost regular uniform hypergraphs with small codegrees.
--
--   **Formalization Note** $S(v)$ and $\deg_T(v)$ are `incident S A v` and the cardinality of `incident T A v`; disjointness and the matching property are stated with `Disjoint` and `Set.Pairwise`. The factor $r-1$ is natural-number subtraction cast to the reals, which equals $r-1$ since $r\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Nibble.lean#L537-L691

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

theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.one_round (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) {D ε C a K : ℝ}
    (hD : 1 ≤ D) (he : 0 ≤ ε) (hequarter : ε ≤ D/4) (hC : 0 ≤ C)
    (ha : 0 < a) (ha16 : a ≤ 1/16) (hra : (r : ℝ)*a ≤ 1/4)
    (hK : 0 ≤ K) (hcode : U.card*C ≤ K*D) (hCa : C ≤ a*D)
    (hsize : 512*(r : ℝ) ≤ a*U.card)
    (hmany : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*U.card)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) :
    ∃ W : Finset V, ∃ T M : Finset E,
      W ⊆ U ∧ T ⊆ S ∧ (∀ e ∈ T, A e ⊆ W) ∧ M ⊆ S ∧
      (M : Set E).Pairwise (fun e f ↦ Disjoint (A e) (A f)) ∧
      Disjoint W (M.biUnion A) ∧
      ((W.card : ℝ) ≤ (1-a/2)*U.card) ∧
      (((U \ (W ∪ M.biUnion A)).card : ℝ) ≤ (16*(r : ℝ)+1)*a^2*U.card) ∧
      ∀ v ∈ W, |((incident T A v).card : ℝ) - (1-((r-1 : ℕ) : ℝ)*a)*D| ≤
        (1+2*(r : ℝ)*a)*ε + 8*(r : ℝ)^2*a^2*D := by sorry
