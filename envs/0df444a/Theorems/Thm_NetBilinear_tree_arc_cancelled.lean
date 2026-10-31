-- Prove2me | Theorems.Thm_NetBilinear_tree_arc_cancelled
-- name    : NetBilinear.tree_arc_cancelled
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:06.649508+00:00
-- url     : https://prove2.me/theorems/16f75f36-b98d-44ec-9030-c12cb14cc313
-- title:
--   Theorem 2, proof (pp.7–8): every arc with both ends in the tree has its term $y_1x_r$ canceled
-- statement:
--   Let $G=(V,A)$ be a finite network without self-loops, with tail $t(k)$ and head $h(k)$ of each arc $k$ (parallel arcs allowed, no connectivity assumed), and let $\bar G$ be its undirected variant. Let $\bar T$ be a tree in $\bar G$ with node set $\tilde I\subseteq V$, let $l\in A$ be an arc incident to exactly one node of $\bar T$, and let $\tilde I_1,\tilde I_2$ be a partition of $\tilde I$ ($\tilde I_1\cap\tilde I_2=\emptyset$, $\tilde I_1\cup\tilde I_2=\tilde I$; either part may be empty).
--
--   The four parts of Theorem 2 are described by a sign $s\in\{+,-\}$ for the rows of $\tilde I_1$ and the opposite sign $-s$ for the rows of $\tilde I_2$: the assignment is $[\{i^{s}\}_{i\in\tilde I_1},\{i^{-s}\}_{i\in\tilde I_2}]$, the rows of the first set multiplied by $y_1$ (weight $\gamma_t=1$) and those of the second by $1-y_1$ (weight $\theta_t=1$). If $h(l)\in\tilde I$ the base equality has class $l^{s}$ (parts (i) and (ii)); if $t(l)\in\tilde I$ it has class $l^{-s}$ (parts (iii) and (iv)).
--
--   Then for every arc $r$ with $t(r)\in\tilde I$ and $h(r)\in\tilde I$, the bilinear term $y_1x_r$ is created and canceled in the aggregation, i.e. its aggregated coefficient
--   $$\sigma[r=l]+\sum_{i\in\tilde I_1}E_{i^{s},r}-\sum_{i\in\tilde I_2}E_{i^{-s},r}$$
--   is $0$, in each of the four parts.
--
--   This is the step of the proof of Theorem 2 that produces $|R|$ cancellations, one for each arc of the tree $T$.
--
--   **Formalization Note** The network is `Network V A` with `tail`, `head` and `loopless`; $\bar G$ is the `SimpleGraph` `G.underlying`, and the tree is a subgraph `T` with `T.verts = Ĩ` whose induced graph is a tree. Rows of the augmented incidence matrix are pairs $(i,s)\in V\times\{+,-\}$ with $E_{i^s,k}=s([t(k)=i]-[h(k)=i])$; `rowsWith s X` is $\{i^s\}_{i\in X}$.
--
--   Differences from the source:
--   - reading: a network G = (V,A) (self-loops not mentioned) → Network has the field loopless: no arc is a self-loop; reason: a node-arc incidence matrix (p.4) has no self-loop column; for a loop l at a node v ∈ Ĩ, l is incident to exactly one node and h(l) ∈ Ĩ, but y₁x_l occurs only in the base equality and never cancels, so (C2) fails
--   - encoding: T̄ a tree in the (multi)graph Ḡ with node set Ĩ → a subgraph T of the SimpleGraph G.underlying with T.verts = Ĩ and T.coe.IsTree; reason: a tree on Ĩ exists in the multigraph Ḡ iff one exists in its simple collapse; same instances
--   - encoding: l is incident to exactly one node of T̄ → Xor (t(l) ∈ Ĩ) (h(l) ∈ Ĩ); reason: equivalent since t(l) ≠ h(l)
--   - encoding: EC&R assignment [I₁,…,I_m, Ī | J, J̄] (p.3) → the reduced m = 1 form [I₁, Ī] (J = J̄ = ∅), rows V × Sign, weights γ, θ ≥ 0; reason: Remark 1 (p.5) reduces the m = 1 assignment to [I₁, Ī], the form Theorem 2 writes; (C1), (C2) are those of p.3 with J = J̄ = ∅
--   - reading: a bilinear term is canceled "(i.e., their coefficient becomes zero)" → the term is created (nonzero contribution) by some used constraint and its aggregated coefficient is 0; reason: (C2) speaks of terms "created" and then "canceled"; counting terms that never appear would make (C1) hold for free
--   - generalization: each arc r ∈ R, the arcs of the directed variant T of the tree → every arc r with t(r) ∈ Ĩ and h(r) ∈ Ĩ; reason: every arc of T has both ends in Ĩ, so the statement specializes to the source; with parallel arcs the arc corresponding to a tree edge is not unique
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, Theorem 2, proof, pp.7–8, "for each r ∈ R, the only constraints in the aggregation that contain xr are the flow-balance constraints corresponding to the head node h(r) and tail node t(r) of r" … "we obtain at least |R| cancellations during the aggregation corresponding to the arcs of T"

import Mathlib
import Definitions.Def_NetBilinear_Network
import Definitions.Def_NetBilinear_IsECRAssignmentOne
import Definitions.Def_NetBilinear_Network_IsECRAssignment

namespace NetBilinear

/-- **Proof of Theorem 2, pp.7–8: the term `y₁x_r` of every arc `r` with both ends in the tree
is canceled.**
arXiv:2302.14151v2, Theorem 2, proof, pp.7–8: "for each r ∈ R, the only constraints in the
aggregation that contain xr are the flow-balance constraints corresponding to the head node h(r)
and tail node t(r) of r … As a result, we obtain at least |R| cancellations during the
aggregation corresponding to the arcs of T."

Hypotheses (those of Theorem 2, p.7): `G` is a finite network without self-loops, `T` is a
tree in `Ḡ` (a subgraph of `G.underlying` whose induced graph `T.coe` is a tree) with node set
`Ĩ = Itil`, the arc `l` is incident to exactly one node of `T` (`Xor`), and `(Ĩ₁, Ĩ₂) =
(I1, I2)` is a partition of `Ĩ` (either part may be empty).

The four parts are given by a sign `s` for the rows of `Ĩ₁` (the rows of `Ĩ₂` carry the
opposite sign `s.flip`) and the endpoint of `l` in `Ĩ`: if `h(l) ∈ Ĩ` the class is `l^s`
(parts (i) for `s = +`, (ii) for `s = −`); if `t(l) ∈ Ĩ` the class is `l^{−s}` (parts (iii)
for `s = −`, (iv) for `s = +`). Every used constraint gets weight `1`: `γ = 1` on `I₁ =
rowsWith s Ĩ₁`, `θ = 1` on `Ī = rowsWith s.flip Ĩ₂` (proof, p.7, "added with").

For every arc `r` with `t(r) ∈ Ĩ` and `h(r) ∈ Ĩ`, the term `y₁x_r` is created and canceled.

**Formalization Note.** The paper speaks of the arcs `r ∈ R` of the directed variant `T` of
the tree; every such arc has both ends in `Ĩ`, and the statement is posed for all arcs with
both ends in `Ĩ` (with parallel arcs, the arc "corresponding" to a tree edge is not unique). -/
theorem tree_arc_cancelled {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (G : Network V A) (Itil : Finset V) (T : G.underlying.Subgraph)
    (hT : T.verts = (Itil : Set V)) (hTree : T.coe.IsTree) (l : A)
    (hl : Xor (G.tail l ∈ Itil) (G.head l ∈ Itil))
    (I1 I2 : Finset V) (hdisj : Disjoint I1 I2) (hunion : I1 ∪ I2 = Itil) (s : Sign) (r : A)
    (hr_tail : G.tail r ∈ Itil) (hr_head : G.head r ∈ Itil) :
    (G.head l ∈ Itil →
        IsCancelled G.incRow l s (rowsWith s I1) (rowsWith s.flip I2)
          (fun _ => 1) (fun _ => 1) r) ∧
    (G.tail l ∈ Itil →
        IsCancelled G.incRow l s.flip (rowsWith s I1) (rowsWith s.flip I2)
          (fun _ => 1) (fun _ => 1) r) := by sorry

end NetBilinear
