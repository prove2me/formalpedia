-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_almost_perfect_matching
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.almost_perfect_matching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:21:46.932332+00:00
-- url     : https://prove2.me/theorems/24757730-4719-403d-b81a-902d63454e79
-- title:
--   Almost perfect matchings in nearly regular uniform hypergraphs with small codegrees
-- statement:
--   Fix an integer $r\ge 1$ and real numbers $K_0\ge 0$ and $\eta>0$. A finite $r$-uniform multi-hypergraph is described by a finite vertex set $U$, a finite set $S$ of edge labels, and an assignment $i\mapsto A(i)$ of a finite vertex set to each label. For a vertex $v$ let $\deg(v)=|\{i\in S: v\in A(i)\}|$ be its degree, and for vertices $v\ne w$ let $\operatorname{codeg}(v,w)=|\{i\in S: v\in A(i)\text{ and } w\in A(i)\}|$ be their codegree.
--
--   **Theorem.** There exist constants $e>0$ and $T>0$, depending only on $r$, $K_0$ and $\eta$, with the following property. Let $U,S,A$ be as above and let $D,C$ be real numbers such that
--
--   1. $D\ge T$ and $|U|\ge T$;
--   2. $0\le C\le eD$ and $|U|\,C\le K_0D$;
--   3. every edge $i\in S$ satisfies $A(i)\subseteq U$ and $|A(i)|=r$;
--   4. every vertex $v\in U$ satisfies $|\deg(v)-D|\le eD$;
--   5. any two distinct vertices $v,w\in U$ satisfy $\operatorname{codeg}(v,w)\le C$.
--
--   Then there is a set $M\subseteq S$ of edges with pairwise disjoint vertex sets that covers all but an $\eta$-fraction of $U$:
--
--   $$
--   A(i)\cap A(j)=\varnothing\quad\text{for all } i\ne j \text{ in } M,\qquad r\,|M|\ \ge\ (1-\eta)\,|U| .
--   $$
--
--   Because the edges of $M$ are disjoint $r$-subsets of $U$, the number $r|M|$ is exactly the number of covered vertices, so $M$ is an almost perfect matching. This is a quantitative form of the classical almost-perfect-matching theorem for nearly regular hypergraphs with small codegrees, proved by the semi-random ("nibble") method; here the codegree bound is $C\le eD$ and the codegrees are additionally normalized by $|U|C\le K_0D$. In the construction of flat Littlewood polynomials it supplies the near-perfect packings of the slot hypergraphs.
--
--   **Formalization Note** Vertices and edge labels live in arbitrary types `V` and `E` (in `Type`, with `E` finite); edges are indexed by labels rather than given as sets, so repeated edges are allowed. The degree is the cardinality of `incident S A v`, the set of labels $i\in S$ with $v\in A(i)$, and the codegree is the cardinality of the intersection of two such sets. The constants $e,T$ are chosen before the types `V`, `E` are quantified, so they are uniform over all hypergraphs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Nibble.lean#L991-L1070

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
open Filter Topology

theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.almost_perfect_matching (r : ℕ) (hr : 1 ≤ r) {K₀ η : ℝ}
    (hK₀ : 0 ≤ K₀) (hη : 0 < η) :
    ∃ e T : ℝ, 0 < e ∧ 0 < T ∧
    ∀ {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E],
    ∀ (U : Finset V) (S : Finset E) (A : E → Finset V) (D C : ℝ),
      T ≤ D → T ≤ (U.card : ℝ) → 0 ≤ C → C ≤ e*D →
      U.card*C ≤ K₀*D →
      (∀ i ∈ S, A i ⊆ U) → (∀ i ∈ S, (A i).card = r) →
      (∀ v ∈ U, |((incident S A v).card : ℝ)-D| ≤ e*D) →
      (∀ v ∈ U, ∀ w ∈ U, v ≠ w →
        ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) →
      ∃ M ⊆ S, (M : Set E).Pairwise (fun i j ↦ Disjoint (A i) (A j)) ∧
        (1-η)*(U.card : ℝ) ≤ r*(M.card : ℝ) := by sorry
