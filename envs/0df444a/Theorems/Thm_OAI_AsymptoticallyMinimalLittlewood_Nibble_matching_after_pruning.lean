-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_matching_after_pruning
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.matching_after_pruning
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:22:27.803538+00:00
-- url     : https://prove2.me/theorems/eb4d9430-a1fe-4f52-b390-bc0273fe39c7
-- title:
--   Almost perfect matchings after deleting a small set of irregular vertices
-- statement:
--   Fix an integer $r\ge 1$ and real numbers $K_0\ge0$ and $\eta>0$. A finite $r$-uniform multi-hypergraph is given by a finite vertex set $U$, a finite set $S$ of edge labels and finite vertex sets $A(i)$ for $i\in S$. Write $\deg(v)=|\{i\in S: v\in A(i)\}|$ for the degree of a vertex $v$ and $\operatorname{codeg}(v,w)=|\{i\in S: v\in A(i)\text{ and }w\in A(i)\}|$ for the codegree of two vertices.
--
--   **Theorem.** There exist constants $e>0$ and $T>0$, depending only on $r$, $K_0$ and $\eta$, such that the following holds. Let $U,S,A$ be as above, let $B\subseteq U$ be a set of exceptional vertices, and let $D,C$ be real numbers with
--
--   1. $D\ge T$ and $|U\setminus B|\ge T$;
--   2. $0\le C\le eD$, $\ |U|\,C\le K_0D$ and $|B|\,C\le eD/2$;
--   3. $A(i)\subseteq U$ and $|A(i)|=r$ for every $i\in S$;
--   4. $|\deg(v)-D|\le eD/2$ for every $v\in U\setminus B$;
--   5. $\operatorname{codeg}(v,w)\le C$ for all distinct $v,w\in U$.
--
--   Then there is a set $M\subseteq S$ of edges with pairwise disjoint vertex sets such that
--
--   $$
--   A(i)\cap A(j)=\varnothing\quad\text{for all } i\ne j\text{ in }M,\qquad r\,|M|\ \ge\ (1-\eta)\,|U\setminus B| .
--   $$
--
--   No degree condition is imposed on the vertices of $B$: they may be arbitrarily irregular, provided the total codegree loss $|B|\,C$ is small compared with $eD$. This is the form in which the almost-perfect-matching theorem is applied in the slot-packing part of the construction of flat Littlewood polynomials, where $B$ collects the vertices whose degree deviates too much from its expected value.
--
--   **Formalization Note** Degrees and codegrees are cardinalities of `incident S A v` and of intersections of two such sets. Vertices and labels live in arbitrary types `V`, `E` in `Type` (with `E` finite), and the constants $e,T$ are chosen before these types are quantified.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Matching.lean#L37-L66

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
universe uV uE
open scoped BigOperators
open Finset
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.matching_after_pruning (r : ℕ) (hr : 1≤r) {K₀ η : ℝ}
    (hK₀ : 0≤K₀) (hη : 0<η) :
    ∃ e T : ℝ, 0<e ∧ 0<T ∧
    ∀ {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E],
    ∀ (U B : Finset V) (S : Finset E) (A : E → Finset V) (D C : ℝ),
      B⊆U → T≤D → T≤((U\B).card : ℝ) → 0≤C → C≤e*D →
      U.card*C≤K₀*D → B.card*C≤e*D/2 →
      (∀ i∈S, A i⊆U) → (∀ i∈S, (A i).card=r) →
      (∀ v∈U\B, |((incident S A v).card : ℝ)-D|≤e*D/2) →
      (∀ v∈U, ∀ w∈U, v≠w → ((incident S A v∩incident S A w).card : ℝ)≤C) →
      ∃ M⊆S, (M : Set E).Pairwise (fun i j ↦ Disjoint (A i) (A j)) ∧
        (1-η)*((U\B).card : ℝ)≤r*(M.card : ℝ) := by sorry
