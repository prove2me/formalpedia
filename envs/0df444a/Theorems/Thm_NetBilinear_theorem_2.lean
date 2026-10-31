-- Prove2me | Theorems.Thm_NetBilinear_theorem_2
-- name    : NetBilinear.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:15.920354+00:00
-- url     : https://prove2.me/theorems/e5d2436f-5609-4070-831e-4bc8a25a6239
-- title:
--   Theorem 2: a tree meeting exactly one endpoint of $l$ gives EC&R assignments of class $l^\pm$ for every partition of its nodes
-- statement:
--   Let $G=(V,A)$ be a finite network without self-loops, with tail $t(k)$ and head $h(k)$ of each arc $k$ (parallel arcs allowed, no connectivity assumed), and let $\bar G$ be its undirected variant. Let $\bar T$ be a tree in $\bar G$ with node set $\tilde I\subseteq V$, let $l\in A$ be an arc incident to exactly one node of $\bar T$, and let $\tilde I_1,\tilde I_2$ be a partition of $\tilde I$ ($\tilde I_1\cap\tilde I_2=\emptyset$, $\tilde I_1\cup\tilde I_2=\tilde I$; either part may be empty).
--
--   Then:
--
--   1. if $h(l)\in\tilde I$, then $[\{i^+\}_{i\in\tilde I_1},\{i^-\}_{i\in\tilde I_2}]$ is an EC&R assignment for class-$l^+$;
--   2. if $h(l)\in\tilde I$, then $[\{i^-\}_{i\in\tilde I_1},\{i^+\}_{i\in\tilde I_2}]$ is an EC&R assignment for class-$l^-$;
--   3. if $t(l)\in\tilde I$, then $[\{i^-\}_{i\in\tilde I_1},\{i^+\}_{i\in\tilde I_2}]$ is an EC&R assignment for class-$l^+$;
--   4. if $t(l)\in\tilde I$, then $[\{i^+\}_{i\in\tilde I_1},\{i^-\}_{i\in\tilde I_2}]$ is an EC&R assignment for class-$l^-$.
--
--   Here $[\mathcal I_1,\bar{\mathcal I}]$ is an EC&R assignment for $m=1$: the rows in $\mathcal I_1$ are multiplied by $\gamma_t y_1$, those in $\bar{\mathcal I}$ by $\theta_t(1-y_1)$, the base equality $y_1x_l-z_l=0$ by $\pm1$, with some nonnegative weights for which (C1) at least $|\mathcal I_1|+|\bar{\mathcal I}|$ bilinear terms are canceled and (C2) every used constraint has a canceled term.
--
--   Together with Proposition 2 of the paper (every non-trivial facet comes from such a tree), this gives a graphical description of all EC&R assignments for one $y$ variable: trees of the network that contain exactly one end of the base arc generate the cutting planes of the convex hull of the bilinear set.
--
--   **Formalization Note** The network is `Network V A` with `tail`, `head` and `loopless`; $\bar G$ is the `SimpleGraph` `G.underlying`, and the tree is a subgraph `T` with `T.verts = Ĩ` whose induced graph is a tree. Rows of the augmented incidence matrix are pairs $(i,s)\in V\times\{+,-\}$ with $E_{i^s,k}=s([t(k)=i]-[h(k)=i])$; `rowsWith s X` is $\{i^s\}_{i\in X}$.
--
--   Differences from the source:
--   - reading: a network G = (V,A) (self-loops not mentioned) → Network has the field loopless: no arc is a self-loop; reason: a node-arc incidence matrix (p.4) has no self-loop column; for a loop l at a node v ∈ Ĩ, l is incident to exactly one node and h(l) ∈ Ĩ, but y₁x_l occurs only in the base equality and never cancels, so (C2) fails
--   - encoding: T̄ a tree in the (multi)graph Ḡ with node set Ĩ → a subgraph T of the SimpleGraph G.underlying with T.verts = Ĩ and T.coe.IsTree; reason: a tree on Ĩ exists in the multigraph Ḡ iff one exists in its simple collapse; same instances
--   - encoding: l is incident to exactly one node of T̄ → Xor (t(l) ∈ Ĩ) (h(l) ∈ Ĩ); reason: equivalent since t(l) ≠ h(l)
--   - encoding: EC&R assignment [I₁,…,I_m, Ī | J, J̄] (p.3) → the reduced m = 1 form [I₁, Ī] (J = J̄ = ∅), rows V × Sign, weights γ, θ ≥ 0; reason: Remark 1 (p.5) reduces the m = 1 assignment to [I₁, Ī], the form Theorem 2 writes; (C1), (C2) are those of p.3 with J = J̄ = ∅
--   - reading: a bilinear term is canceled "(i.e., their coefficient becomes zero)" → the term is created (nonzero contribution) by some used constraint and its aggregated coefficient is 0; reason: (C2) speaks of terms "created" and then "canceled"; counting terms that never appear would make (C1) hold for free
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, Theorem 2, p.7

import Mathlib
import Definitions.Def_NetBilinear_Network
import Definitions.Def_NetBilinear_IsECRAssignmentOne
import Definitions.Def_NetBilinear_Network_IsECRAssignment

namespace NetBilinear

/-- **Theorem 2: every tree meeting exactly one endpoint of `l` gives EC&R assignments of class
`l±` for every partition of its nodes.**
Khademnia & Davarnia, *Convexification of Bilinear Terms over Network Polytopes*,
arXiv:2302.14151v2, Theorem 2, p.7: "Consider set S1 with Ξ that represents the network
polytope corresponding to the network G = (V,A). Let T̄ be a tree in Ḡ with the node set Ĩ ⊆ V,
and let l ∈ A be an arc that is incident to exactly one node of T̄. Then, for any partition Ĩ1
and Ĩ2 of Ĩ (i.e., Ĩ1 ∩ Ĩ2 = ∅ and Ĩ1 ∪ Ĩ2 = Ĩ), we have that
(i) if h(l) ∈ Ĩ, then [{i+}i∈Ĩ1, {i−}i∈Ĩ2] is an EC&R assignment for class-l+,
(ii) if h(l) ∈ Ĩ, then [{i−}i∈Ĩ1, {i+}i∈Ĩ2] is an EC&R assignment for class-l−,
(iii) if t(l) ∈ Ĩ, then [{i−}i∈Ĩ1, {i+}i∈Ĩ2] is an EC&R assignment for class-l+,
(iv) if t(l) ∈ Ĩ, then [{i+}i∈Ĩ1, {i−}i∈Ĩ2] is an EC&R assignment for class-l−."

Hypotheses (those of Theorem 2, p.7): `G` is a finite network without self-loops, `T` is a
tree in `Ḡ` (a subgraph of `G.underlying` whose induced graph `T.coe` is a tree) with node set
`Ĩ = Itil`, the arc `l` is incident to exactly one node of `T` (`Xor`), and `(Ĩ₁, Ĩ₂) =
(I1, I2)` is a partition of `Ĩ` (either part may be empty).

**Formalization Note.** "EC&R assignment" is the reduced `m = 1` form `[I₁, Ī]` of Remark 1
(p.5), `Network.IsECRAssignment`: disjoint row sets with some nonnegative weights satisfying
(C1) and (C2). The first slot `I₁` (rows multiplied by `y₁`) and the second `Ī` (rows
multiplied by `1 − y₁`) are `rowsWith s X`, the rows `i^s`, `i ∈ X`. The network has no
self-loops (field `loopless`): for a loop `l` at a node of `Ĩ` the statement is false. -/
theorem theorem_2 {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (G : Network V A) (Itil : Finset V) (T : G.underlying.Subgraph)
    (hT : T.verts = (Itil : Set V)) (hTree : T.coe.IsTree) (l : A)
    (hl : Xor (G.tail l ∈ Itil) (G.head l ∈ Itil))
    (I1 I2 : Finset V) (hdisj : Disjoint I1 I2) (hunion : I1 ∪ I2 = Itil) :
    (G.head l ∈ Itil →
        G.IsECRAssignment l .pos (rowsWith .pos I1) (rowsWith .neg I2)) ∧
    (G.head l ∈ Itil →
        G.IsECRAssignment l .neg (rowsWith .neg I1) (rowsWith .pos I2)) ∧
    (G.tail l ∈ Itil →
        G.IsECRAssignment l .pos (rowsWith .neg I1) (rowsWith .pos I2)) ∧
    (G.tail l ∈ Itil →
        G.IsECRAssignment l .neg (rowsWith .pos I1) (rowsWith .neg I2)) := by sorry

end NetBilinear
