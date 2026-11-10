-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_6_8
-- name    : LoadBalMatch.Main.lemma_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:33:11.335736+00:00
-- url     : https://prove2.me/theorems/3b562158-cfac-4e2f-be84-b4984c1c1015
-- title:
--   Lemma 6.8 — loads of a balanced fractional matching on the Gallai–Edmonds decomposition (items 1–4)
-- statement:
--   Let $H$ be a graph on the finite set $V$ with Gallai–Edmonds decomposition $V=D\cup A\cup C$ and components $D_1,\dots,D_r$ of $H[D]$, and let $x$ be a balanced fractional matching on $H$ with loads $x_v$ and levels $\ell_v$ (in $H$). Then:
--   1. $x_v=1$ for every $v\in V\setminus D$;
--   2. $x$ is constant on every component $D_i$ (its value is written $x_i$);
--   3. every $A$-vertex sends flow only to its least loaded $D$-neighbours:
--   $$x_{a,v}>0\ \Longrightarrow\ v\in D\ \text{ and }\ x_v=\ell_a=\min_{u\in N_H(a)\cap D}x_u\qquad\forall a\in A,\ \forall v\in N_H(a);$$
--   4. the graph $H'=(V,\operatorname{supp}(x))$ has the same Gallai–Edmonds decomposition $(D,A,C)$ as $H$, and $H'[D]$ has the same connected components $D_1,\dots,D_r$.
--
--   Item 4 is what allows the algorithm to replace its stored graph by the support of $x$.
--
--   Differences from the source:
--   - encoding: x_v = ℓ_a = min_{u∈N_H(a)∩D} x_u → load x v = level H x a and load x v ≤ load x u for every u ∈ N_H(a) ∩ D; reason: v itself lies in N_H(a) ∩ D, so the two conditions say that x_v is that minimum
--   - encoding: H′[D] has connected components D_1, …, D_r → SameDComp (supportGraph x) u v ↔ SameDComp H u v for all u, v; reason: two partitions of D are equal iff they have the same 'same block' relation
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 28, Lemma 6.8

import Mathlib
import Definitions.Def_LoadBalMatch_Main_FracMatching
import Definitions.Def_LoadBalMatch_Main_GallaiEdmonds

namespace LoadBalMatch.Main

theorem lemma_6_8 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (x : Sym2 V → ℝ) (hx : IsBalanced H x) :
    (∀ v, v ∉ gD H → load x v = 1) ∧
    (∀ u v, SameDComp H u v → load x u = load x v) ∧
    (∀ a ∈ gA H, ∀ v, H.Adj a v → 0 < x s(a, v) →
      v ∈ gD H ∧ load x v = level H x a ∧
        ∀ u, H.Adj a u → u ∈ gD H → load x v ≤ load x u) ∧
    (gD (supportGraph x) = gD H ∧ gA (supportGraph x) = gA H ∧ gC (supportGraph x) = gC H ∧
      ∀ u v, SameDComp (supportGraph x) u v ↔ SameDComp H u v) := by sorry

end LoadBalMatch.Main
