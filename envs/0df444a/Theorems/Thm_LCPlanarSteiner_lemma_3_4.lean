-- Prove2me | Theorems.Thm_LCPlanarSteiner_lemma_3_4
-- name    : LCPlanarSteiner.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:59.956813+00:00
-- url     : https://prove2.me/theorems/9cc62640-5ed4-4643-939e-8d1af5149bb1
-- title:
--   Lemma 3.4 — original-prefix invariant (3) carries to separator contacts and to the child at depth $d+1$
-- statement:
--   Let $(C, B, E_R)$ be a region of a graph with nonnegative costs and lengths, $H, \Gamma, \delta > 0$, $S$ the separator vertices ($B' = B \cup S$), $F$ the old purchased union and $F' \supseteq F$ the union after buying the separator and its profiles. Assume that the arrivals $A$ satisfy Lemma 3.2 with the old labels ($A(v) \le \mathrm{dist}_F(r, b) + \ell(Q)$ for every owned simple path $Q : b \rightsquigarrow v$, $b \in B$, $c(Q) \le \Gamma$), and that the profiles give every $v \in S$ with $A(v) \le M$ an arrival $\mathrm{dist}_{F'}(r, v) \le A(v) + \delta$.
--
--   **Lemma 3.4 (Original-prefix invariant).** Let $p : r \rightsquigarrow t$ be an original simple path with $\ell(p) \le H$, let $b$ be its last vertex in $B$, and suppose
--   $$
--   p[b, t] \subseteq E_R,\qquad \mathrm{dist}_F(r, b) \le \ell(p[r, b]) + d\delta . \tag{3}
--   $$
--   If $c(p[b, t]) \le \Gamma$ and $H + d\delta \le M$, then
--   1. every separator contact $v \in S$ of $p$ after $b$ has $\mathrm{dist}_{F'}(r, v) \le \ell(p[r, v]) + (d+1)\delta$;
--   2. if $t$ lies in a child ($t \in C \setminus S$), then, with $b'$ the last vertex of $p$ in $B'$, the suffix $p[b', t]$ uses only owned arcs of the child containing $t$ and $\mathrm{dist}_{F'}(r, b') \le \ell(p[r, b']) + (d+1)\delta$: the same full path satisfies (3) in the child at depth $d + 1$.
--
--   The comparison is always with the prefix of the same original witness, so restricting to a child does not restart its clock.
--
--   **Formalization Note** Positions index the vertex sequence of $p$. The child is the weak component of $t$ in the separator host, built from $K_R$ with horizon $H$ and estimate $\Gamma$.
--
--   Differences from the source:
--   - generalization: the separator paths of §3.1, the arrivals of Lemma 3.2 and the profiles of Lemma 3.3 → an arbitrary vertex set S and arbitrary arrivals A and purchases F′ ⊇ F with the two stated properties; reason: the proof uses only these properties, which the construction of §3.1 provides
--   - encoding: "its last old-boundary vertex b", "a separator contact v after b", "t lies in a child" → b at position k with no later vertex in B; v ∈ S at a position after k; t ∈ C \ S, the child being the weak component of t in K_R \ S; reason: Lean convention for the paper's notions
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.4, p.6; setting §3.1, pp.5–6

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsSPath
import Definitions.Def_LCPlanarSteiner_plen
import Definitions.Def_LCPlanarSteiner_DistLE
import Definitions.Def_LCPlanarSteiner_IsRegion
import Definitions.Def_LCPlanarSteiner_childArcs

namespace LCPlanarSteiner

/-- **Lemma 3.4 (Original-prefix invariant).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.4, p.6: "Let p : r ⇝ t be an original path of length at most H. At depth d, let b be
its last old-boundary vertex and suppose p[b, t] ⊆ E_R, dist_F(r, b) ≤ ℓ(p[r, b]) + dδ. (3) If
c(p[b, t]) ≤ Γ and H + dδ ≤ M, every separator contact v after b receives arrival at most
ℓ(p[r, v]) + (d + 1)δ. If t lies in a child, the same full path satisfies (3) there at depth d + 1."
Setting, §3.1, pp.5–6: arrivals are computed "with the old F, then buy the separator and its
profile extensions"; children own `E_i = {uv ∈ E_R : v ∈ C_i, u ∈ B′ ∪ C_i}`.

Let `R = (C, B, E_R)` be a region of a well-formed graph, `H, Γ, δ > 0`, `S` the separator vertices
(`B′ = B ∪ S`), `F` the old purchased union and `F′ ⊇ F` the union after buying the separator and
its profiles. Assume:
* the arrivals `A` satisfy Lemma 3.2's comparison for budget `Γ` with the old labels:
  `A(v) ≤ dist_F(r, b) + ℓ(Q)` for every owned simple path `Q : b ⇝ v`, `b ∈ B`, `c(Q) ≤ Γ`;
* the profile purchases satisfy Lemma 3.3's conclusion on `S`: every `v ∈ S` with `A(v) ≤ M` has
  `dist_{F′}(r, v) ≤ A(v) + δ`.
Let `p` be a simple path from `r` to `t` with `ℓ(p) ≤ H`, and `b` its vertex at position `k`, the
last vertex of `p` in `B`, with `p[b, t] ⊆ E_R`, `dist_F(r, b) ≤ ℓ(p[r, b]) + dδ` (3),
`c(p[b, t]) ≤ Γ` and `H + dδ ≤ M`. Then
1. every vertex `v ∈ S` of `p` after `b` has `dist_{F′}(r, v) ≤ ℓ(p[r, v]) + (d + 1)δ`;
2. if `t ∈ C \ S` (`t` lies in a child), then `p` has a last vertex `b′` in `B′`, at a position
   `k′ ≥ k`, such that `p[b′, t]` uses only owned arcs of the child containing `t` and
   `dist_{F′}(r, b′) ≤ ℓ(p[r, b′]) + (d + 1)δ`: (3) at depth `d + 1`.

**Formalization Note.** Positions index the vertex sequence of `p` (`vtx`); `p[r, v]` and `p[b, v]`
are `take`/`drop` of the arc list. The separator `S` and the purchases `F′` are arbitrary sets with
the two stated properties (the proof uses nothing else about the separator paths, the query
algorithm or the profile). The child is the weak component of `t` in the separator host
(`childArcs`, built from `K_R` with horizon `H` and estimate `Γ`). -/
theorem lemma_3_4 (G : Net) (hG : G.WF) (C B ER : Finset ℕ) (hR : IsRegion G C B ER)
    (H Γ M δ : ℚ) (d : ℕ) (hH : 0 < H) (hΓ : 0 < Γ) (hδ : 0 < δ)
    (S F F' : Finset ℕ) (hFF' : F ⊆ F') (r : ℕ) (A : ℕ → WithTop ℚ)
    (hA : ∀ b ∈ B, ∀ (v : ℕ) (Q : List ℕ), IsSPath G b v Q → (∀ e ∈ Q, e ∈ ER) →
      lcost G Q ≤ Γ → ∀ W : List ℕ, IsWalk G r b W → (∀ e ∈ W, e ∈ F) →
        ∃ a : ℚ, A v = a ∧ a ≤ plen G W + plen G Q)
    (hprof : ∀ v ∈ S, ∀ a : ℚ, A v = a → a ≤ M → DistLE G F' r v (a + δ))
    (t : ℕ) (p : List ℕ) (hp : IsSPath G r t p) (hpH : plen G p ≤ H)
    (k : ℕ) (hk : k ≤ p.length) (hb : vtx G r p k ∈ B)
    (hlast : ∀ j, k < j → j ≤ p.length → vtx G r p j ∉ B)
    (hsuf : ∀ e ∈ p.drop k, e ∈ ER)
    (h3 : DistLE G F r (vtx G r p k) (plen G (p.take k) + d * δ))
    (hcost : lcost G (p.drop k) ≤ Γ) (hM : H + d * δ ≤ M) :
    (∀ j, k < j → j ≤ p.length → vtx G r p j ∈ S →
      DistLE G F' r (vtx G r p j) (plen G (p.take j) + (d + 1) * δ)) ∧
    (t ∈ C → t ∉ S →
      ∃ k', k ≤ k' ∧ k' ≤ p.length ∧ (vtx G r p k' ∈ B ∨ vtx G r p k' ∈ S) ∧
        (∀ j, k' < j → j ≤ p.length → vtx G r p j ∉ B ∧ vtx G r p j ∉ S) ∧
        (∀ e ∈ p.drop k', e ∈ childArcs G C B ER H Γ S t) ∧
        DistLE G F' r (vtx G r p k') (plen G (p.take k') + (d + 1) * δ)) := by sorry

end LCPlanarSteiner
