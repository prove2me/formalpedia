-- Prove2me | Theorems.Thm_LocalSepDecomp_theorem_8_21
-- name    : LocalSepDecomp.theorem_8_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:50.17622+00:00
-- url     : https://prove2.me/theorems/a9e7d116-9360-48c3-9a0e-a48e78b8e88f
-- title:
--   Theorem 8.21∗ — $H(N)$ is the folding of $H(\hat N)$ via $p_r$
-- statement:
--   Let $G$ be a locally finite, connected graph with $(k-1)r<\Delta_r(G)$, and assume $(\ast)$: $r\ge 2$ or $k=1$. Let $N$ be a nested set of $r$-local separations of $G$ with $r$-tomic separators of size at most $k$, let $(H,\mathcal G)=H(N)$, let $\hat N$ be the set of all lifts of elements of $N$ to $G_r$, and let $\bar H(N)=(\bar H,\bar{\mathcal G})$ be the graph-decomposition of $G$ obtained from $H(\hat N)$ by folding via $p_r$. For a cutout $\sigma$ of $N$ let $\tau(\sigma)$ be the set of cutouts $\hat\sigma$ of $\hat N$ with $p_r(\hat\sigma)=\sigma$, and for $s\in N$ let $\tau(s)$ be the set of all lifts of $s$. Then
--
--   1. $\tau=(\sigma\mapsto\tau(\sigma),\ s\mapsto\tau(s))$ is an isomorphism $H\to\bar H$, and
--   2. $G_\sigma=\bar G_{\tau(\sigma)}$ for every node $\sigma$ of $H$.
--
--   Differences from the source:
--   - encoding: the r-local covering $p_r : G_r \to G$, unique up to isomorphism of coverings → an arbitrary covering $p : C \to G$ with `IsLocalCovering G r p` (characteristic subgroup = the r-local subgroup), on a vertex type in the universe of $V$; reason: the paper constructs $G_r$ only up to isomorphism; every statement holds for one such covering iff for all, and one exists in the universe of $V$ (walks modulo the r-local subgroup)
--   - reading: $\tau$ defined on the cutouts of $N$ → for $N=\emptyset$ (no cutouts), $\tau$ sends the single node of $H(\emptyset)$ to the class of the single node of $H(\hat N)=H(\emptyset)$; reason: the paper's statement presupposes cutouts; both decompositions are then the trivial one-node decomposition with part $G$
--   - encoding: nodes and edges of $\bar H$ are $D(p_r)$-orbits → classes of the relation 'related by a deck transformation' on cutouts and on elements of $\hat N$; ends and parts computed from representatives; reason: Construction 2.6 with the natural action of $D(p_r)$
--   - encoding: $(k-1)r<\Delta_r(G)$ → `DisplacementBound p r k`; reason: integer arithmetic with $\Delta_r(G)\in\mathbb N\cup\{\infty\}$
--   - reading: $s \succ t$ (used without a separate definition) and crossing/$\succcurlyeq$ defined for $r$-local separations with $r$-tomic separators → $s \succ t$ is $s \succcurlyeq t \wedge s \ne t$; the crossing and $\succcurlyeq$ conditions are defined for all pairs; reason: strict part of $\succcurlyeq$, as $>$ for $\geqslant$ in §8.1; the statement only applies them to separations with $r$-tomic separators
--   - encoding: orders $|X|$ of separators → `Set.encard` in $\mathbb N_\infty$; reason: separators of the infinite cover can be infinite (p.29); no finite instance changes
--   - encoding: $G$ locally finite → every neighbour set is finite (a `Prop`, not Mathlib's data-carrying `LocallyFinite` class); reason: same graphs
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 8.21∗, p.55

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts

set_option autoImplicit false

namespace LocalSepDecomp

open SimpleGraph

universe u

/-- **Theorem 8.21∗.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 8.21∗, p.55.
Let `G` be a locally finite, connected graph with `(k − 1) r < Δ_r(G)`, and assume (∗) `r ≥ 2` or
`k = 1`. Let `N` be a nested set of `r`-local separations of `G` with `r`-tomic separators of size
`≤ k`, `(H, G) := H(N)`, `N̂` the set of all lifts of the elements of `N` to `G_r`, and
`H̄(N) = (H̄, Ḡ)` the graph-decomposition of `G` obtained from `H(N̂)` by folding via `p_r`. Let
`τ(σ)` be the set of all cutouts `σ̂` of `N̂` with `p_r(σ̂) = σ`, and `τ(s)` the set of all lifts of
`s ∈ N`. Then (i) `τ = (σ ↦ τ(σ), s ↦ τ(s))` is an isomorphism `H → H̄`, and (ii) `G_σ = Ḡ_{τ(σ)}`
for every node `σ` of `H`.

**Formalization Note.** `G_r` is any `r`-local covering `p`. `IsTauIso` says that the node and edge
bijections of `ψ` are the maps `τ`; for `N = ∅` (no cutouts) `τ` sends the trivial node of `H(∅)`
to the class of the trivial node of `H(N̂) = H(∅)`. -/
theorem theorem_8_21 {V W : Type u} (G : SimpleGraph V) (hlf : IsLocallyFinite G)
    (hG : G.Connected) (r k : ℕ) (C : SimpleGraph W) (p : C →g G) (hp : IsLocalCovering G r p)
    (hΔ : DisplacementBound p r k) (hstar : 2 ≤ r ∨ k = 1) (N : Set (ULSep V))
    (hN : ∀ u ∈ N, IsULSep G r u ∧ IsRTomic G r u.X ∧ u.X.encard ≤ k)
    (hnest : ULSetNested G r N) :
    ∃ ψ : DecompIso (Hdecomp G r N) (foldedH p r (liftSet p r N)),
      IsTauIso p r N (liftSet p r N) ψ := by sorry

end LocalSepDecomp
