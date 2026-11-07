-- Prove2me | Theorems.Thm_GyoriLovasz_proposition_3_2_network
-- name    : GyoriLovasz.proposition_3_2_network
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:22.865252+00:00
-- url     : https://prove2.me/theorems/6e1aadc4-eabc-4a07-9c6d-1dd38bd78cc2
-- title:
--   Proposition 3.2 — essential terminals from one maximum flow (network and correctness; time bound: theorem_2)
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T\subseteq V$, $k=|T|$, no self-loops and no edge leaving a terminal, and fix $v\in V\setminus T$. Let $H$ be the vertex-splitting network of the proof (pp.18–19) with $K=k+1$. Then:
--
--   1. $H$ has $2|V|+2$ nodes and $|V|+1+|E|+|T|$ arcs;
--   2. an integral maximum $s_{\mathrm{in}}$–$s_{\mathrm{out}}$ flow exists;
--   3. for **every** integral maximum flow $f$: its value is $\kappa_G(v)$; the sets $L_C,S_C,R_C$ read off the vertices from which $s_{\mathrm{out}}$ is reachable in the residual graph of $f$ form the tightest minimum cut separating $v$ from $T$; and a terminal $t$ is essential for $v$ if and only if $t\in S_C$.
--
--   Proposition 3.2 states that the essential terminals of $v$ can be computed by one maximum-flow computation in a network with $O(n)$ vertices and $O(n+m)$ edges, followed by linear-time postprocessing. This item states the network, its size and the correctness of the postprocessing; the cost of the computation, as part of a polynomial-time algorithm, is carried by the machine statement `theorem_2`.
--
--   Differences from the source:
--
--   - reading: "can be computed using one maximum-flow computation in a network with O(n) vertices and O(n + m) edges and linear-time postprocessing"; "In particular, this takes O((n + m)^{1+o(1)}) time" [VCK+23] → the explicit network H of the proof with exactly 2|V| + 2 nodes and |V| + 1 + |E| + |T| arcs, existence of an integral maximum flow, and correctness of reading the tightest cut and the essential terminals off every integral maximum flow; no running time; reason: the claim is about an idealized computation with no machine model; its cost inside an algorithm is the machine statement theorem_2, and the cited [VCK+23] bound is an external result (paper.md decision 9)
--   - encoding: "Let f be an integral maximum flow" (proof, p.18) → the conclusion for every integral maximum flow f; reason: the proof's f is arbitrary
--   - encoding: the standing assumption of §2, p.14: terminals are vertices, no self-loops or parallel edges, terminals have no outgoing edges (stated once, "without loss of generality") → explicit hypotheses `Std G T` and `T ⊆ G.verts`; parallel edges are impossible in `DG`; reason: trap 19: a section's standing assumption is a hypothesis of each of its results
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Proposition 3.2 and its proof, pp.18–19

import Mathlib
import Definitions.Def_GyoriLovasz_IsEssential
import Definitions.Def_GyoriLovasz_IsCut
import Definitions.Def_GyoriLovasz_Std
import Definitions.Def_GyoriLovasz_SplitNetwork

namespace GyoriLovasz

variable {V : Type*} [DecidableEq V]

/-- **Proposition 3.2, the network and its correctness (time bound: `theorem_2`).** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Proposition 3.2, p.18: "For a fixed
vertex v ∈ V \ T, the set of terminals essential for v can be computed using one maximum-flow computation in a network with
O(n) vertices and O(n + m) edges and linear-time postprocessing."

On the explicit network `H` of the proof (pp.18–19), which has `2|V| + 2` nodes and `|V| + 1 + |E| + |T|` arcs, an integral
maximum flow exists, and every integral maximum flow `f` has value `κ_G(v)`; the sets `L_C`, `S_C`, `R_C` read off the reverse
residual reachability of `s_out` form the tightest minimum cut, and the essential terminals are exactly the terminals in `S_C`.

**Formalization Note.** The machine cost of the proposition is carried by `theorem_2`; the clause on [VCK+23] is not posed.
The statement is for every integral maximum flow, including one that carries a cycle through `v`. -/
theorem proposition_3_2_network (G : DG V) (T : Finset V) (v : V) (hstd : Std G T) (hT : T ⊆ G.verts)
    (hv : v ∈ G.verts \ T) :
    (SplitNetwork.nodes G).card = 2 * G.verts.card + 2 ∧
      (SplitNetwork.arcs G T v).card = G.verts.card + 1 + G.arcs.card + T.card ∧
      (∃ f, SplitNetwork.IsMaxFlow G T v f) ∧
      ∀ f, SplitNetwork.IsMaxFlow G T v f →
        SplitNetwork.value G T v f = kappa G T v ∧
          IsTightest G T v (SplitNetwork.cutL G T v f) (SplitNetwork.cutS G T v f)
            (SplitNetwork.cutR G T v f) ∧
          ∀ t ∈ T, (IsEssential G T v t ↔ t ∈ SplitNetwork.cutS G T v f) := by sorry

end GyoriLovasz
