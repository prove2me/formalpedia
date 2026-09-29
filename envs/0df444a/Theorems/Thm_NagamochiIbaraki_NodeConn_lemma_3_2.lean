-- Prove2me | Theorems.Thm_NagamochiIbaraki_NodeConn_lemma_3_2
-- name    : NagamochiIbaraki.NodeConn.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:10:37.70931+00:00
-- url     : https://prove2.me/theorems/f525cff6-e9a5-4466-80ee-d192c9bd75cf
-- title:
--   Lemma 3.2 — for a node cut W = {w_1, …, w_i} of G_{i+1}, right after w_t is scanned, E*_t crosses X–Y only through w_t and E*_j (t < j ≤ i + 1) not at all
-- statement:
--   Let $G = (V, E)$ be a simple graph with $|V| \ge 2$, let $E_1, \dots, E_{|E|}$ be the final classes of a completed run of Procedure FOREST on $G$, and let $1 \le i$ with $i + 1 \le |E|$. Put $G_{i+1} = (V, E_1 \cup \dots \cup E_{i+1})$.
--
--   Let $W$ be a set of $i$ nodes that is a **node cut set** of $G_{i+1}$, its nodes denoted $w_1, w_2, \dots, w_i$ in the order in which FOREST scans them. Let $X$ be a component of $G_{i+1} - W$ and let $Y$ be the set of nodes of $G_{i+1} - W$ outside $X$ (possibly several components), with $Y \ne \emptyset$.
--
--   Take any $w_t \in W$ and consider the instant immediately after FOREST has scanned $w_t$ (marked it scanned at line 11); let $E^*_j$ denote the classes at that instant. Then:
--
--   1. every path $P_t \subseteq E^*_t$ connecting a node of $X$ to a node of $Y$ passes through $w_t$;
--   2. for every $j$ with $t + 1 \le j \le i + 1$, $E^*_j$ has no path connecting a node of $X$ to a node of $Y$.
--
--   Part 2 for $w_i$ is what the proof of Theorem 3.1 uses: after all of $W$ is scanned, $E_{i+1}$ has no $X$–$Y$ path.
--
--   **Formalization Note** $X$ is the set of nodes outside $W$ reachable from a fixed node $x_0 \notin W$ in $G_{i+1} - W$; $Y$ is the set of nodes outside $W \cup X$, and the cut hypothesis is that $Y$ is nonempty. The instant is the state right after the step at which $w_t$ enters the set of scanned nodes, and the index $t$ is the number of nodes of $W$ scanned at that state, i.e. the position of $w_t$ in $W$'s scan order.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), pp. 591–592, Lemma 3.2 (a), (b)

import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_localNodeConn
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

namespace NagamochiIbaraki.NodeConn

theorem lemma_3_2
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hsimple : Function.Injective ends)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K)
    (i : ℕ) (hi : 1 ≤ i) (hiE : i + 1 ≤ Fintype.card E)
    (W : Finset V) (hW : W.card = i)
    (x₀ : V) (hx₀ : x₀ ∉ W)
    (hcut : ∃ b : V, b ∉ W ∧ ¬ ConnAvoid ends (upto (σ K) (i + 1)) W x₀ b)
    (n : ℕ) (hn : n < K) (w : V) (hwW : w ∈ W)
    (hw₀ : w ∉ (σ n).done) (hw₁ : w ∈ (σ (n + 1)).done) :
    -- X: the component of G_{i+1} − W containing x₀; Y: the rest of G_{i+1} − W;
    -- t: the position of w among the nodes of W in the order scanned by FOREST.
    let X : V → Prop := fun v => v ∉ W ∧ ConnAvoid ends (upto (σ K) (i + 1)) W x₀ v
    let Y : V → Prop := fun v => v ∉ W ∧ ¬ ConnAvoid ends (upto (σ K) (i + 1)) W x₀ v
    let t : ℕ := ((σ (n + 1)).done ∩ W).card
    -- (a)
    (∀ a b : V, X a → Y b →
      ∀ p : (edgeGraph ends (cls (σ (n + 1)) t)).Walk a b, p.IsPath → w ∈ p.support) ∧
    -- (b)
    (∀ j : ℕ, t + 1 ≤ j → j ≤ i + 1 → ∀ a b : V, X a → Y b →
      ¬ (edgeGraph ends (cls (σ (n + 1)) j)).Reachable a b) := by sorry

end NagamochiIbaraki.NodeConn
