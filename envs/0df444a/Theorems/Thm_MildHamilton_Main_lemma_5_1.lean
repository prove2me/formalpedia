-- Prove2me | Theorems.Thm_MildHamilton_Main_lemma_5_1
-- name    : MildHamilton.Main.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:51.508975+00:00
-- url     : https://prove2.me/theorems/72e99a8a-1b50-487b-ab5b-19aa8c716496
-- title:
--   Lemma 5.1, p. 11 — a perfect matching after perturbation
-- statement:
--   Let $H_0$ be a balanced bipartite graph with bipartition $(L_0,R_0)$, where $|L_0|=|R_0|=m$. Suppose $H_0$ is $p$-cut-dense and $d_{H_0}(v)=(1\pm\eta)D$ for every $v\in V(H_0)$. Set $\alpha=pm/D$, and suppose $0<\alpha\le1/2$ and $\eta\le\alpha/10$.
--
--   Let $X,Y$ be disjoint sets with $|X|=|Y|$, and let $H$ be a bipartite graph with bipartition $(L_0\cup X,R_0\cup Y)$ containing $H_0$. Suppose every $x\in X$ has at least $D/2$ neighbours in $R_0$, every $y\in Y$ has at least $D/2$ neighbours in $L_0$, and
--
--   $$d_H(v,X)\le\frac{\alpha D}{20}\ \text{ for every }v\in R_0,\qquad d_H(v,Y)\le\frac{\alpha D}{20}\ \text{ for every }v\in L_0.$$
--
--   Then $H$ contains a perfect matching.
--
--   This gives the perfect matchings between consecutive layers once redistributed vertices have been added.
--
--   **Formalization Note** The vertex set of $H$ is a finite type partitioned into $L_0,R_0,X,Y$, and $H_0$ lives on the subtype of $L_0\cup R_0$, so that cut density is measured in $V(H_0)$.
--
--   Differences from the source:
--   - encoding: d_{H_0}(v) = (1 ± η)D with D, η unsigned → |d_{H_0}(v) − D| ≤ ηD with 0 < D and 0 ≤ η; reason: the ± notation presupposes a positive scale D and a nonnegative error η
--   - encoding: X, Y disjoint sets → L_0, R_0, X, Y pairwise disjoint with union the vertex type of H; reason: the bipartition (L_0 ∪ X, R_0 ∪ Y) and the use on p. 13 presuppose this
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Lemma 5.1, p. 11

import Mathlib
import Definitions.Def_MildHamilton_Main_Spectral

namespace MildHamilton.Main

open Classical in
/-- Lemma 5.1 (Muyesser, STOC 2027 submission #233, p. 11): perfect matching after perturbation. The vertex set
of `H` is the type `W`, partitioned into `L₀`, `R₀`, `X`, `Y`; the graph `H₀` lives on `L₀ ∪ R₀`, and
`d_{H₀}(v) = (1 ± η) D` means `|d_{H₀}(v) − D| ≤ η D`. -/
theorem lemma_5_1 {W : Type*} [Fintype W] (L₀ R₀ X Y : Finset W) (m : ℕ) (p η D : ℝ)
    (hLR : Disjoint L₀ R₀) (hLX : Disjoint L₀ X) (hLY : Disjoint L₀ Y) (hRX : Disjoint R₀ X)
    (hRY : Disjoint R₀ Y) (hXY : Disjoint X Y) (hcover : L₀ ∪ R₀ ∪ X ∪ Y = Finset.univ)
    (hL : L₀.card = m) (hR : R₀.card = m) (hXYcard : X.card = Y.card)
    (H₀ : SimpleGraph {v // v ∈ L₀ ∪ R₀}) (H : SimpleGraph W)
    (hH₀bip : H₀.IsBipartiteWith {v | (v : W) ∈ L₀} {v | (v : W) ∈ R₀})
    (hHbip : H.IsBipartiteWith (↑(L₀ ∪ X) : Set W) (↑(R₀ ∪ Y) : Set W))
    (hsub : ∀ u v, H₀.Adj u v → H.Adj (u : W) (v : W))
    (hcut : IsCutDense H₀ p) (hD : 0 < D) (hη : 0 ≤ η)
    (hdeg : ∀ v, |(H₀.degree v : ℝ) - D| ≤ η * D)
    (hα0 : 0 < p * m / D) (hα1 : p * m / D ≤ 1 / 2) (hηα : η ≤ p * m / D / 10)
    (hX : ∀ x ∈ X, D / 2 ≤ (nbrCount H x R₀ : ℝ))
    (hY : ∀ y ∈ Y, D / 2 ≤ (nbrCount H y L₀ : ℝ))
    (hRdeg : ∀ v ∈ R₀, (nbrCount H v X : ℝ) ≤ p * m / D * D / 20)
    (hLdeg : ∀ v ∈ L₀, (nbrCount H v Y : ℝ) ≤ p * m / D * D / 20) :
    ∃ M : H.Subgraph, M.IsPerfectMatching := by sorry

end MildHamilton.Main
