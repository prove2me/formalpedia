-- Prove2me | Theorems.Thm_NetBilinear_condition_C1
-- name    : NetBilinear.condition_C1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:57.710046+00:00
-- url     : https://prove2.me/theorems/58dc1b8f-e269-4222-8476-fe22456b5a88
-- title:
--   Theorem 2, proof (p.8): condition (C1) holds with unit weights
-- statement:
--   Let $G=(V,A)$ be a finite network without self-loops, with tail $t(k)$ and head $h(k)$ of each arc $k$ (parallel arcs allowed, no connectivity assumed), and let $\bar G$ be its undirected variant. Let $\bar T$ be a tree in $\bar G$ with node set $\tilde I\subseteq V$, let $l\in A$ be an arc incident to exactly one node of $\bar T$, and let $\tilde I_1,\tilde I_2$ be a partition of $\tilde I$ ($\tilde I_1\cap\tilde I_2=\emptyset$, $\tilde I_1\cup\tilde I_2=\tilde I$; either part may be empty).
--
--   The four parts of Theorem 2 are described by a sign $s\in\{+,-\}$ for the rows of $\tilde I_1$ and the opposite sign $-s$ for the rows of $\tilde I_2$: the assignment is $[\{i^{s}\}_{i\in\tilde I_1},\{i^{-s}\}_{i\in\tilde I_2}]$, the rows of the first set multiplied by $y_1$ (weight $\gamma_t=1$) and those of the second by $1-y_1$ (weight $\theta_t=1$). If $h(l)\in\tilde I$ the base equality has class $l^{s}$ (parts (i) and (ii)); if $t(l)\in\tilde I$ it has class $l^{-s}$ (parts (iii) and (iv)).
--
--   Then in each of the four parts, condition (C1) holds for these unit weights: the number of canceled bilinear terms is at least
--   $$|\{i^{s}\}_{i\in\tilde I_1}|+|\{i^{-s}\}_{i\in\tilde I_2}|=|\tilde I_1|+|\tilde I_2|.$$
--
--   In the paper this count is $|R|+1$: one cancellation per arc of the tree, whose number of arcs is $|\tilde I|-1$, plus the base arc $l$.
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
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, Theorem 2, proof, p.8, "in total we have at least |R| + 1 = |Ĩ1| + |Ĩ2| cancellations during the aggregation of the constraints in the EC&R assignment, showing the satisfaction of condition (C1)"

import Mathlib
import Definitions.Def_NetBilinear_Network
import Definitions.Def_NetBilinear_IsECRAssignmentOne
import Definitions.Def_NetBilinear_Network_IsECRAssignment

namespace NetBilinear

/-- **Proof of Theorem 2, p.8: condition (C1) holds with unit weights.**
arXiv:2302.14151v2, Theorem 2, proof, p.8: "As a result, in total we have at least
|R| + 1 = |Ĩ1| + |Ĩ2| cancellations during the aggregation of the constraints in the EC&R
assignment, showing the satisfaction of condition (C1) of the EC&R procedure."

Hypotheses (those of Theorem 2, p.7): `G` is a finite network without self-loops, `T` is a
tree in `Ḡ` (a subgraph of `G.underlying` whose induced graph `T.coe` is a tree) with node set
`Ĩ = Itil`, the arc `l` is incident to exactly one node of `T` (`Xor`), and `(Ĩ₁, Ĩ₂) =
(I1, I2)` is a partition of `Ĩ` (either part may be empty).

The four parts are given by a sign `s` for the rows of `Ĩ₁` (the rows of `Ĩ₂` carry the
opposite sign `s.flip`) and the endpoint of `l` in `Ĩ`: if `h(l) ∈ Ĩ` the class is `l^s`
(parts (i) for `s = +`, (ii) for `s = −`); if `t(l) ∈ Ĩ` the class is `l^{−s}` (parts (iii)
for `s = −`, (iv) for `s = +`). Every used constraint gets weight `1`: `γ = 1` on `I₁ =
rowsWith s Ĩ₁`, `θ = 1` on `Ī = rowsWith s.flip Ĩ₂` (proof, p.7, "added with").

At least `|I₁| + |Ī| = |Ĩ₁| + |Ĩ₂|` bilinear terms are canceled (`CondC1`). -/
theorem condition_C1 {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (G : Network V A) (Itil : Finset V) (T : G.underlying.Subgraph)
    (hT : T.verts = (Itil : Set V)) (hTree : T.coe.IsTree) (l : A)
    (hl : Xor (G.tail l ∈ Itil) (G.head l ∈ Itil))
    (I1 I2 : Finset V) (hdisj : Disjoint I1 I2) (hunion : I1 ∪ I2 = Itil) (s : Sign) :
    (G.head l ∈ Itil →
        CondC1 G.incRow l s (rowsWith s I1) (rowsWith s.flip I2)
          (fun _ => 1) (fun _ => 1)) ∧
    (G.tail l ∈ Itil →
        CondC1 G.incRow l s.flip (rowsWith s I1) (rowsWith s.flip I2)
          (fun _ => 1) (fun _ => 1)) := by sorry

end NetBilinear
