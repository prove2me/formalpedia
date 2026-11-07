-- Prove2me | Theorems.Thm_MinBisectFPT_proof_theorem_1_1_reduction
-- name    : MinBisectFPT.proof_theorem_1_1_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:22.999358+00:00
-- url     : https://prove2.me/theorems/ab272cee-5e25-4157-8dbb-b3225a7f715c
-- title:
--   Proof of Theorem 1.1: convolution over components, the case $k=0$, the root table
-- statement:
--   Let $G$ be a graph on $n$ vertices.
--
--   1. For all $k$, all $\ell$ and all $j\le k$, the coefficient of $y^\ell z^j$ in the product over the components $G_i$ of $G$ of the polynomials
--   $$\sum_{\ell',\,j'\le k}C_{G_i}(\ell',j')\,y^{\ell'}z^{j'}$$
--   is $C_G(\ell,j)$.
--   2. If $G$ is connected, then $C_G(\ell,0)=1$ for $\ell\in\{0,n\}$ and $C_G(\ell,0)=0$ otherwise.
--   3. If $(T,\beta)$ is a rooted tree decomposition of $G$ with root $r$, then $\sigma(r)=\emptyset$, $\alpha(r)=V(G)$, $G_r=G$, and $C_r(\emptyset,\ell,j)=C_G(\ell,j)$ for all $\ell,j$.
--
--   These three facts reduce Theorem 1.1 to connected graphs with $k\ge1$ and to the computation of the root table.
--
--   Differences from the source:
--   - encoding: a component $G_i$ → `G.induce c.supp` for `c : G.ConnectedComponent`; reason: same graph
--   - reading: the product "with all monomials of $z$-degree above $k$ discarded" → the coefficient at each $j\le k$ of the product of the factors truncated at $z^k$; reason: discarding in the factors and in the product gives the same coefficients at $j\le k$
--   - generalization: the convolution "if $G$ is disconnected" → every graph $G$; reason: a connected graph has one component, where the identity is trivial, so the disconnected case is an instance
--   - generalization: the root identity under the standing assumptions of §4 ($G$ connected, $k\ge1$, (D1)–(D3), $j\le k$, $\ell\le|\alpha|$) → any rooted tree decomposition of any $G$, all $\ell,j$; reason: it uses only $\sigma(\mathrm{root})=\emptyset$ and that the root's cone is $V(G)$; the page's decompositions are instances
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Proof of Theorem 1.1, p.15; §4.1, p.11

import Mathlib
import Definitions.Def_MinBisectFPT_countPoly
import Definitions.Def_MinBisectFPT_NodeCtx

open scoped Classical

namespace MinBisectFPT

/-- **Proof of Theorem 1.1, the reductions.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Proof of Theorem 1.1, p.15, with the root
identity of §4.1, p.11. (a) `Σ_{ℓ,j} C_G(ℓ, j) y^ℓ z^j` is the product of the polynomials of the
components, modulo monomials of `z`-degree above `k`; (b) the connected case at `k = 0`; (c) at the root of
a rooted tree decomposition `σ = ∅`, `α = V(G)`, `G_root = G`, and `C_root(∅, ℓ, j) = C_G(ℓ, j)`.

**Formalization Note** A component `G_i` is `G.induce c.supp`. -/
theorem proof_theorem_1_1_reduction {n : ℕ} (G : SimpleGraph (Fin n)) :
    (∀ k l j : ℕ, j ≤ k →
      MvPolynomial.coeff (Finsupp.single 0 l + Finsupp.single 1 j)
        (∏ c : G.ConnectedComponent, countPoly (G.induce c.supp) k) = countSets G l j) ∧
    (G.Connected → ∀ l : ℕ, countSets G l 0 = if l = 0 ∨ l = n then 1 else 0) ∧
    (∀ (T : RootedTD n) (r : Fin T.N), IsRootedTD G T → T.parent r = none →
      T.adhesion r = ∅ ∧ T.component r = Finset.univ ∧ subtreeGraph G T r = G ∧
        ∀ l j : ℕ, tableCount G T r ∅ l j = countSets G l j) := by sorry

end MinBisectFPT
