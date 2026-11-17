-- Prove2me | Theorems.Thm_LocalSepDecomp_Supplement_theorem_3_13
-- name    : LocalSepDecomp.Supplement.theorem_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:48:04.678824+00:00
-- url     : https://prove2.me/theorems/f2b5a0df-c976-4dd5-be0e-913215e9f77e
-- title:
--   Theorem 3.13 — $N(G_r)$ is a canonical tree of tangles of $G_r$ of infinite scope, and $T(N(G_r))$ a canonical tangle tree-decomposition
-- statement:
--   Let $G$ be a finite connected graph and $r\in\mathbb N$, and let $p_r:G_r\to G$ be the $r$-local covering. Then $N(G_r)$ is a canonical tree of tangles of the $r$-local covering $G_r$ of infinite scope. Moreover, $T(N(G_r))$ is a canonical tangle tree-decomposition of $G_r$ of infinite scope.
--
--   Here $N(G_r)=\bigcup_kN^k(G_r)$ is built by Construction 3.6 from the set of all bottlenecks of the (in general infinite) graph $G_r$, and $T(N)$ is the candidate of Construction 2.3. A tree of tangles, or a tangle tree-decomposition, has **infinite scope** if it has scope $k$ for every $k\in\mathbb N$. Canonical means invariant under $\mathrm{Aut}(G_r)$.
--
--   $$\text{for all } k\in\mathbb N:\ N(G_r)\text{ is a tree of tangles of scope }k,\ \text{ and }T(N(G_r))\text{ a tangle tree-decomposition of scope }k.$$
--
--   Folding this decomposition along $p_r$ gives the canonical graph-decompositions of [DJKK26] that the paper's local construction recovers below $K(G,r)$.
--
--   **Formalization Note** $G_r$ is any $r$-local covering $p:C\to G$; all are isomorphic. The conclusion also states that every orientation of every separation in $N(G_r)$ lies in a splitting star, which is what makes $T(N(G_r))$ defined (p.17).
--
--   Differences from the source:
--
--   - reading: T(N(G_r)) is a (canonical tangle) tree-decomposition → every element of ori(N(G_r)) lies in a splitting star (AllOriInSplittingStars), and Tdecomp C (N(C)) is a tangle tree-decomposition of every scope k and Aut(C)-canonical; reason: T(N) of Construction 2.3 is defined only when every orientation lies in a splitting star (p.17); the claim presupposes it, so it is asserted (the stronger reading)
--   - encoding: the r-local covering G_r → any r-local covering p : C → G (IsLocalCovering G r p), for every r ∈ ℕ, C of the same universe as V and possibly infinite; reason: all r-local coverings are isomorphic (p.13); the base goal uses the same convention
--   - encoding: N(G_r) (no set B named); infinite scope → Nfull C = Nall of Construction 3.6 with B the set of all bottlenecks of C; ∀ k : ℕ, scope k; reason: p.21: without reference to B, B is the set of all bottlenecks; p.23: infinite scope is scope k for every k ∈ ℕ
--   - encoding: canonical → IsCanonicalUSepSet C ⊤ and IsCanonicalDecomp ⊤; reason: canonical means Aut(G_r)-canonical (pp.14, 17)
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 3.13, p.23

import Mathlib
import Definitions.Def_LocalSepDecomp_Supplement_TreeFromNested

set_option autoImplicit false

namespace LocalSepDecomp.Supplement

open SimpleGraph

universe u

/-- **Theorem 3.13.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via
Local Separations*, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…),
Theorem 3.13, p.23. Let `G` be a finite connected graph. Then `N(G_r)` is a canonical tree of
tangles of the `r`-local covering `G_r` of infinite scope. Moreover, `T(N(G_r))` is a canonical
tangle tree-decomposition of `G_r` of infinite scope.

**Formalization Note.** `G_r` is any `r`-local covering `p : C → G` (all are isomorphic), for every
`r ∈ ℕ`; `C` is in general infinite. `N(C) = ⋃_k N^k(C)` for the set of all bottlenecks of `C`
(`Nfull`). Infinite scope (p.23) is scope `k` for every `k ∈ ℕ`. "Canonical" is
`Aut(C)`-canonical (`Γ = ⊤`). Since `T(N)` of Construction 2.3 is only defined when every element
of `ori(N)` lies in a splitting star (p.17), that is asserted as part of the conclusion. -/
theorem theorem_3_13 {V W : Type u} [Finite V] (G : SimpleGraph V) (hG : G.Connected) (r : ℕ)
    (C : SimpleGraph W) (p : C →g G) (hp : IsLocalCovering G r p) :
    ((∀ k : ℕ, IsTreeOfTangles C k (Nfull C)) ∧ IsCanonicalUSepSet C ⊤ (Nfull C)) ∧
      (AllOriInSplittingStars C (Nfull C) ∧
        (∀ k : ℕ, IsTangleTreeDecomp C k (Tdecomp C (Nfull C))) ∧
        IsCanonicalDecomp ⊤ (Tdecomp C (Nfull C))) := by sorry

end LocalSepDecomp.Supplement
