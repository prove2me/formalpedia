-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_nibble_iteration
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_iteration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:20:35.776556+00:00
-- url     : https://prove2.me/theorems/8a6dbaf3-1589-42f0-805e-0ad0358b9564
-- title:
--   Iterated nibble: after $k$ rounds few vertices remain active and little is wasted
-- statement:
--   Let $V$ be a set of vertices and $E$ a finite set of edge labels. A hypergraph is given by a finite set $S\subseteq E$ of edges together with a finite vertex set $A_e\subseteq V$ for every label $e$. For a vertex $v$ let $S(v)=\{e\in S: v\in A_e\}$ be the set of edges containing $v$ and $\deg_S(v)=|S(v)|$ its degree; for vertices $v\ne w$ the number $|S(v)\cap S(w)|$ is their codegree.
--
--   Fix a finite vertex set $U\subseteq V$. A *packing state* for $(U,S)$ is a triple $(U',S',M)$ consisting of an active vertex set $U'\subseteq U$, an active edge set $S'\subseteq S$ with $A_e\subseteq U'$ for every $e\in S'$, and a set $M\subseteq S$ of chosen edges which is a matching ($A_e\cap A_f=\emptyset$ for distinct $e,f\in M$) and whose covered vertices $\bigcup_{e\in M}A_e$ are disjoint from $U'$.
--
--   Let $r\ge1$ and $k\ge0$ be integers and $D,\varepsilon,C,a,K,d$ real numbers with $D>0$, $\varepsilon\ge0$, $C\ge0$, $0<a\le1/16$, $ra\le1/4$, $K\ge0$ and $d>0$. Put $q=1-(r-1)a$ and assume
--
--   - $1\le q^kD$ and $(1+2ra)^k\big(\varepsilon+8r^2a^2Dk\big)\le q^kD/4$;
--   - $C\le a\,q^kD$ and $|U|\,C\le K\,q^kD$;
--   - $512\,r\le a\,d\,|U|$ and $16\,r^2(K+1)^2\le a^5d\,|U|$;
--   - $(1-a/2)^k\le d$.
--
--   Assume moreover that the hypergraph is $r$-uniform on $U$ ($A_e\subseteq U$ and $|A_e|=r$ for all $e\in S$), almost $D$-regular ($|\deg_S(v)-D|\le\varepsilon$ for all $v\in U$), and has codegrees at most $C$ ($|S(v)\cap S(w)|\le C$ for all distinct $v,w\in U$). Then there is a packing state $(U',S',M)$ with
--
--   $$
--   |U'|\le d\,|U|\qquad\text{and}\qquad\Big|U\setminus\Big(U'\cup\bigcup_{e\in M}A_e\Big)\Big|\le k\,(16r+1)\,a^2\,|U|.
--   $$
--
--   After at most $k$ rounds of the nibble only a $d$-fraction of the vertices is still active, and the vertices discarded without being covered form at most a $k(16r+1)a^2$-fraction. Consequently the matching $M$ covers all but at most $\big(d+k(16r+1)a^2\big)|U|$ vertices of $U$; this is the iterative core of the almost-perfect-matching theorem for almost regular uniform hypergraphs with small codegrees.
--
--   **Formalization Note** Packing states are the structure `PackingState U S A` with fields `vertices`, `edges` and `chosen` (plus the proofs of the listed properties); $S(v)$ is `incident S A v`. The factor $r-1$ is natural-number subtraction cast to the reals, equal to $r-1$ since $r\ge1$. The hypothesis $d>0$ is part of the statement but is not used in the proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Nibble.lean#L769-L916

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

theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_iteration (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) (k : ℕ) {D ε C a K d : ℝ}
    (hD : 0 < D) (he : 0 ≤ ε) (hC : 0 ≤ C)
    (ha : 0 < a) (ha16 : a ≤ 1/16) (hra : (r : ℝ)*a ≤ 1/4)
    (hK : 0 ≤ K) (_hd : 0 < d)
    (hDmin : 1 ≤ (1-((r-1 : ℕ) : ℝ)*a)^k*D)
    (hecap : (1+2*(r : ℝ)*a)^k*(ε+8*(r : ℝ)^2*a^2*D*k) ≤
      (1-((r-1 : ℕ) : ℝ)*a)^k*D/4)
    (hCmin : C ≤ a*((1-((r-1 : ℕ) : ℝ)*a)^k*D))
    (hcode : U.card*C ≤ K*((1-((r-1 : ℕ) : ℝ)*a)^k*D))
    (hsize : 512*(r : ℝ) ≤ a*d*U.card)
    (hmany : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*d*U.card)
    (hcontract : (1-a/2)^k ≤ d)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) :
    ∃ P : PackingState U S A,
      ((P.vertices.card : ℝ) ≤ d*U.card) ∧
      (((U \ (P.vertices ∪ P.chosen.biUnion A)).card : ℝ) ≤
        k*(16*(r : ℝ)+1)*a^2*U.card) := by sorry
