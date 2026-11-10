-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_lemma_4_4
-- name    : MinColorPath.MinorFree.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:14:07.372343+00:00
-- url     : https://prove2.me/theorems/085e2cca-0e30-4587-90c8-deef0acb852d
-- title:
--   Lemma 4.4 — after i rounds every node of height ≤ i is covered by a member of F of size ≤ |P′(x)|
-- statement:
--   In the context of §4, for every run of Algorithm 1 on $(\mathcal G,s,t,w,c)$ and every $0\le i\le n+|P|$, the family $F_i$ produced by the $i$-th iteration ($F_0$ the initial family) satisfies: for every node $x$ of $T$ of height at most $i$ there is $Q\in F_i$ with
--   $$Q \text{ covers } x\quad\text{and}\quad |Q|\le|P'(x)|,\qquad P'(x)=\mathrm{cl}'(\gamma(x)).$$
--   Applied at the root it shows that the final family contains a set no larger than $\mathrm{cl}(V(\pi))$ that connects $s$ to $t$.
--
--   Differences from the source:
--   - reading: the standing context of §4 (p. 21): π ∈ Π_{w,c}, D its 0-diagram, T a (w, c)-good binary tree decomposition of D → hypotheses π.IsPath, 𝒯 : RTD (pathDiag cl 0 π), 𝒯.IsBinary, IsGood 𝒯 w c and IsColoredGraph G P cl; reason: Lemmas 4.1–4.4 are stated in this context (p. 21–22); the lemma's sentence omits it
--   - reading: the family F generated in the i-th iteration of Algorithm 1 → Fs i for every run Fs (IsRun: every choice of minimum-size members in Filter) and every i ≤ n + |P|; Fs 0 is the initial family; reason: every arg min of Algorithm 1 is an arbitrary choice, so the lemma holds for every run; the loop has n + |P| iterations
--   - encoding: the height of a node x in T → 𝒯.height x, the largest distance from x to a node of T_x; reason: the standard height of a rooted tree (leaves have height 0)
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
--   - encoding: a rooted (binary) tree decomposition (T, β) → RTD: the published IsTreeDecomposition on a finite node type plus a root; T_x, γ(x), children and height defined from the root paths; binary = at most two children; reason: the path condition (iii) of the published definition is equivalent to the connected-subtree condition; finite trees as in the paper
--   - encoding: the d-diagram D with vertex set V(G′) ∪ P′, cl′(v) = cl(v), cl′(τ) = {τ}; s, t ∈ β(x) → diagGraph cl d H on the sum type ↥V(G′) ⊕ ↥P′ (G′ = π.toSubgraph for a path), coloring diagCl; s ∈ β(x) is baseIn (the base copy of s lies in the bag); reason: the vertex set is a disjoint union of the base part and the color part
--   - encoding: an (s, t)-path π and its x-segments, the connected components of π[γ(x)] → π : G.Walk s t with π.IsPath; x-segments are the maximal runs [i, j] of consecutive positions of π.support (0-based, from the s-side) inside γ(x); reason: the edges of a path are its consecutive pairs, so the components of π[γ(x)] are exactly these runs
--   - encoding: cdist(G, s, t), the minimum colored length of an (s, t)-path → cdist G cl s t : ℕ∞, ⊤ when there is no path; G − Q is the coloring fun v => cl v \ Q; reason: the minimum over the empty set is +∞; G − Q changes only the coloring
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 24, Lemma 4.4

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_CombineFilter

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Lemma 4.4** (p. 24). In the §4 context, for every run of Algorithm 1 on `(G, s, t, w, c)`
and every `i ≤ n + |P|`, the family `F_i` after the `i`-th iteration contains, for every node `x`
of height at most `i`, a set `Q` that covers `x` with `|Q| ≤ |P'(x)|`. -/
theorem lemma_4_4 {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) (hG : IsColoredGraph G P cl)
    (s t : V) (w c : ℕ) (π : G.Walk s t) (hπ : π.IsPath) (𝒯 : RTD (pathDiag cl 0 π))
    (hbin : 𝒯.IsBinary) (hgood : IsGood 𝒯 w c)
    (Fs : ℕ → Finset (Finset C)) (hrun : IsRun G P cl w c Fs)
    (i : ℕ) (hi : i ≤ Fintype.card V + P.card) (x : 𝒯.T) (hx : 𝒯.height x ≤ i) :
    ∃ Q ∈ Fs i, Covers G cl 𝒯 Q x ∧ Q.card ≤ (𝒯.palBelow x).card := by sorry

end MinColorPath.MinorFree
