-- Prove2me | Theorems.Thm_LocalSepDecomp_lemma_8_23
-- name    : LocalSepDecomp.lemma_8_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:31.569205+00:00
-- url     : https://prove2.me/theorems/77d9f68d-49f4-4443-99d8-4074e4cd1b49
-- title:
--   Lemma 8.23∗ — $H(N)=H(M)/(M\setminus N)$
-- statement:
--   Let $G$ be a locally finite, connected graph with $(k-1)r<\Delta_r(G)$, and assume $(\ast)$: $r\ge 2$ or $k=1$. Let $N\subseteq M$ be nested sets of $r$-local separations of $G$ with $r$-tomic separators of size at most $k$. Then
--   $$H(N)=H(M)/(M\setminus N):$$
--   contracting in $H(M)$ the edges not in $N$ gives $H(N)$, with the same parts.
--
--   This gives clause (iv) of Theorem 1: increasing $k$ refines $H^{\le k}_r(G)$.
--
--   Differences from the source:
--   - encoding: the r-local covering $p_r : G_r \to G$, unique up to isomorphism of coverings → an arbitrary covering $p : C \to G$ with `IsLocalCovering G r p` (characteristic subgroup = the r-local subgroup), on a vertex type in the universe of $V$; reason: the paper constructs $G_r$ only up to isomorphism; every statement holds for one such covering iff for all, and one exists in the universe of $V$ (walks modulo the r-local subgroup)
--   - encoding: equality $H(N)=H(M)/(M\setminus N)$ → an isomorphism of graph-decompositions with parts whose edge map is the identity on $N$; reason: the nodes are cutouts on one side and branch sets on the other, while both edge sets are $N$ (p.56)
--   - encoding: $(k-1)r<\Delta_r(G)$ → `DisplacementBound p r k`; reason: integer arithmetic
--   - reading: $s \succ t$ (used without a separate definition) and crossing/$\succcurlyeq$ defined for $r$-local separations with $r$-tomic separators → $s \succ t$ is $s \succcurlyeq t \wedge s \ne t$; the crossing and $\succcurlyeq$ conditions are defined for all pairs; reason: strict part of $\succcurlyeq$, as $>$ for $\geqslant$ in §8.1; the statement only applies them to separations with $r$-tomic separators
--   - encoding: orders $|X|$ of separators → `Set.encard` in $\mathbb N_\infty$; reason: separators of the infinite cover can be infinite (p.29); no finite instance changes
--   - encoding: $G$ locally finite → every neighbour set is finite (a `Prop`, not Mathlib's data-carrying `LocallyFinite` class); reason: same graphs
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Lemma 8.23∗, p.56

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts

set_option autoImplicit false

namespace LocalSepDecomp

open SimpleGraph

universe u

/-- **Lemma 8.23∗.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Lemma 8.23∗, p.56.
Let `G` be a locally finite, connected graph with `(k − 1) r < Δ_r(G)`, and assume (∗) `r ≥ 2` or
`k = 1`. Let `N ⊆ M` be two nested sets of `r`-local separations of `G` with `r`-tomic separators of
size `≤ k`. Then `H(N) = H(M)/(M ∖ N)`.

**Formalization Note.** The nodes of `H(N)` (cutouts) and of `H(M)/(M ∖ N)` (branch sets) are
different objects, while the edges of both are the elements of `N`; the equality is stated as an
isomorphism of graph-decompositions with parts whose edge map is the identity on `N`. The
hypotheses on `N` (nested, `r`-tomic separators of size `≤ k`) follow from `N ⊆ M`. -/
theorem lemma_8_23 {V W : Type u} (G : SimpleGraph V) (hlf : IsLocallyFinite G)
    (hG : G.Connected) (r k : ℕ) (C : SimpleGraph W) (p : C →g G) (hp : IsLocalCovering G r p)
    (hΔ : DisplacementBound p r k) (hstar : 2 ≤ r ∨ k = 1) (N M : Set (ULSep V)) (hNM : N ⊆ M)
    (hM : ∀ u ∈ M, IsULSep G r u ∧ IsRTomic G r u.X ∧ u.X.encard ≤ k)
    (hMn : ULSetNested G r M) :
    ∃ ψ : DecompIso (Hdecomp G r N) (contract (Hdecomp G r M) {e | e.1 ∉ N}),
      ∀ e, (ψ.edge e).1.1 = e.1 := by sorry

end LocalSepDecomp
