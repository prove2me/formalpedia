-- Prove2me | Theorems.Thm_LocalSepDecomp_theorem_7_18
-- name    : LocalSepDecomp.theorem_7_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:10.408136+00:00
-- url     : https://prove2.me/theorems/0d57a874-638b-4359-aa4d-94c5fdb68a86
-- title:
--   Theorem 7.18∗ — $N^k_r(G_r)$ consists of the lifts of $N^k_r(G)$
-- statement:
--   Let $G$ be a locally finite, connected graph with $(k-1)r<\Delta_r(G)$, and assume $(\ast)$: $r\ge 2$ or $k=1$. Let $\mathcal B_r$ be a set of $r$-local bottlenecks in $G$, and let $\hat{\mathcal B}_r=\{\hat\beta:\beta\in\mathcal B_r\}$, where $\hat\beta$ is the set of all lifts to $G_r$ of the elements of $\beta$ (Lift 7.15). Then:
--
--   1. $N^k_r(G)$ (for $\mathcal B_r$) and $N^k_r(G_r)$ (for $\hat{\mathcal B}_r$) are well-defined;
--   2. $N^k_r(G_r)$ consists precisely of the lifts to $G_r$ of the elements of $N^k_r(G)$;
--   3. the same holds if $\mathcal B_r$ is the set of all $r$-local bottlenecks in $G$ and $\hat{\mathcal B}_r$ the set of all $r$-local bottlenecks in $G_r$;
--   4. in particular $N^k_r(G)$ is nested, and if $\mathcal B_r$ is $\Gamma$-invariant for $\Gamma\le\operatorname{Aut}(G)$, then $N^k_r(G)$ is $\Gamma$-canonical.
--
--   Differences from the source:
--   - encoding: the r-local covering $p_r : G_r \to G$, unique up to isomorphism of coverings → an arbitrary covering $p : C \to G$ with `IsLocalCovering G r p` (characteristic subgroup = the r-local subgroup), on a vertex type in the universe of $V$; reason: the paper constructs $G_r$ only up to isomorphism; every statement holds for one such covering iff for all, and one exists in the universe of $V$ (walks modulo the r-local subgroup)
--   - reading: $N^k_r(G)$ and $N^k_r(G_r)$ are well-defined → all crossing numbers $x^j_r(s)$, $j\le k$, on which $N^k_r$ depends are finite; reason: the count is a cardinal in $\mathbb N_\infty$; $N^k_r$ depends on $N^j_r$ for $j<k$
--   - reading: $s \succ t$ (used without a separate definition) and crossing/$\succcurlyeq$ defined for $r$-local separations with $r$-tomic separators → $s \succ t$ is $s \succcurlyeq t \wedge s \ne t$; the crossing and $\succcurlyeq$ conditions are defined for all pairs; reason: strict part of $\succcurlyeq$, as $>$ for $\geqslant$ in §8.1; the statement only applies them to separations with $r$-tomic separators
--   - encoding: $\hat{\mathcal B}_r$ given by Lift 7.15 applied to $\mathcal B_r$ → $\{\hat\beta:\beta\in\mathcal B_r\}$ with $\hat\beta$ the set of all lifts of elements of $\beta$, for every $\beta\in\mathcal B_r$; reason: Lift 7.15 is the statement that these sets are bottlenecks for orders $\le k$; Construction 7.16 only uses the elements of $\hat{\mathcal B}_r$ that are $j$-bottlenecks
--   - encoding: $(k-1)r<\Delta_r(G)$ → whenever $\Delta_r(G)=n$ is finite, $(k-1)r<n$ in $\mathbb Z$ (`DisplacementBound`); reason: the same inequality with $\Delta_r(G)\in\mathbb N\cup\{\infty\}$
--   - encoding: orders $|X|$ of separators → `Set.encard` in $\mathbb N_\infty$; reason: separators of the infinite cover can be infinite (p.29); no finite instance changes
--   - encoding: $G$ locally finite → every neighbour set is finite (a `Prop`, not Mathlib's data-carrying `LocallyFinite` class); reason: same graphs
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 7.18∗, p.47

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts

set_option autoImplicit false

namespace LocalSepDecomp

open SimpleGraph

universe u

/-- **Theorem 7.18∗** (Nested set). R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 7.18∗, p.47.
Let `G` be a locally finite, connected graph with `(k − 1) r < Δ_r(G)`, and assume (∗) `r ≥ 2` or
`k = 1`. Let `B_r` be a set of `r`-local bottlenecks in `G` and `B̂_r` the set of the sets `β̂` of all
lifts of the elements of `β`, `β ∈ B_r` (Lift 7.15∗). Then `N^k_r(G)` and `N^k_r(G_r)` are
well-defined, and `N^k_r(G_r)` (for `B̂_r`) consists precisely of the lifts to `G_r` of the elements
of `N^k_r(G)` (for `B_r`). The same holds if `B_r` is the set of all `r`-local bottlenecks in `G` and
`B̂_r` the set of all `r`-local bottlenecks in `G_r`. In particular `N^k_r(G)` is nested; and if
`B_r` is `Γ`-invariant, then `N^k_r(G)` is `Γ`-canonical.

**Formalization Note.** `G_r` is any `r`-local covering `p : C → G`. "Well-defined" for `N^k_r` is
read as: all crossing numbers `x^j_r(s)`, `j ≤ k`, on which `N^k_r` depends are finite. -/
theorem theorem_7_18 {V W : Type u} (G : SimpleGraph V) (hlf : IsLocallyFinite G)
    (hG : G.Connected) (r k : ℕ) (C : SimpleGraph W) (p : C →g G) (hp : IsLocalCovering G r p)
    (hΔ : DisplacementBound p r k) (hstar : 2 ≤ r ∨ k = 1) :
    (∀ Br : Set (Set (ULSep V)), (∀ β ∈ Br, ∃ j, IsLocalBottleneck G r j β) →
      (∀ j ≤ k, ∀ s ∈ ⋃₀ localBk G r Br j, lxk G r Br j s < ⊤) ∧
      (∀ j ≤ k, ∀ s ∈ ⋃₀ localBk C r (liftSet p r '' Br) j,
        lxk C r (liftSet p r '' Br) j s < ⊤) ∧
      LNk C r (liftSet p r '' Br) k = liftSet p r (LNk G r Br k) ∧
      ULSetNested G r (LNk G r Br k) ∧
      ∀ Γ : Subgroup (G ≃g G), IsInvariantLBottleneckSet G Γ Br →
        IsCanonicalULSepSet G Γ (LNk G r Br k)) ∧
    ((∀ j ≤ k, ∀ s ∈ ⋃₀ localBk G r (allLBottlenecks G r) j,
        lxk G r (allLBottlenecks G r) j s < ⊤) ∧
      (∀ j ≤ k, ∀ s ∈ ⋃₀ localBk C r (allLBottlenecks C r) j,
        lxk C r (allLBottlenecks C r) j s < ⊤) ∧
      LNk C r (allLBottlenecks C r) k = liftSet p r (LNk G r (allLBottlenecks G r) k) ∧
      ULSetNested G r (LNk G r (allLBottlenecks G r) k) ∧
      ∀ Γ : Subgroup (G ≃g G), IsInvariantLBottleneckSet G Γ (allLBottlenecks G r) →
        IsCanonicalULSepSet G Γ (LNk G r (allLBottlenecks G r) k)) := by sorry

end LocalSepDecomp
