-- Prove2me | Theorems.Thm_LocalSepDecomp_theorem_7_19
-- name    : LocalSepDecomp.theorem_7_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:50.634238+00:00
-- url     : https://prove2.me/theorems/38ab9eda-c890-4299-ac00-a44e581bf61d
-- title:
--   Theorem 7.19∗ — $N^{\le k}_r(G)$ meets every $r$-local bottleneck of order $\le k$
-- statement:
--   Let $G$ be a locally finite, connected graph with $(k-1)r<\Delta_r(G)$, and assume $(\ast)$: $r\ge 2$ or $k=1$. Let $\mathcal B_r$ be a set of $r$-local bottlenecks in $G$. Then $N^{\le k}_r(G)$ (Construction 7.16 for $\mathcal B_r$) meets every $r$-local bottleneck in $\mathcal B_r$ of order at most $k$.
--
--   Differences from the source:
--   - encoding: the r-local covering $p_r : G_r \to G$, unique up to isomorphism of coverings → an arbitrary covering $p : C \to G$ with `IsLocalCovering G r p` (characteristic subgroup = the r-local subgroup), on a vertex type in the universe of $V$; reason: the paper constructs $G_r$ only up to isomorphism; every statement holds for one such covering iff for all, and one exists in the universe of $V$ (walks modulo the r-local subgroup)
--   - encoding: $(k-1)r<\Delta_r(G)$ → `DisplacementBound p r k`; reason: integer arithmetic with $\Delta_r(G)\in\mathbb N\cup\{\infty\}$
--   - reading: $s \succ t$ (used without a separate definition) and crossing/$\succcurlyeq$ defined for $r$-local separations with $r$-tomic separators → $s \succ t$ is $s \succcurlyeq t \wedge s \ne t$; the crossing and $\succcurlyeq$ conditions are defined for all pairs; reason: strict part of $\succcurlyeq$, as $>$ for $\geqslant$ in §8.1; the statement only applies them to separations with $r$-tomic separators
--   - encoding: orders $|X|$ of separators → `Set.encard` in $\mathbb N_\infty$; reason: separators of the infinite cover can be infinite (p.29); no finite instance changes
--   - encoding: $G$ locally finite → every neighbour set is finite (a `Prop`, not Mathlib's data-carrying `LocallyFinite` class); reason: same graphs
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 7.19∗, p.48

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts

set_option autoImplicit false

namespace LocalSepDecomp

open SimpleGraph

universe u

/-- **Theorem 7.19∗.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 7.19∗, p.48.
Let `G` be a locally finite, connected graph with `(k − 1) r < Δ_r(G)`, and assume (∗) `r ≥ 2` or
`k = 1`. Let `B_r` be a set of `r`-local bottlenecks in `G`. Then `N^{≤k}_r(G)` (Construction 7.16
for `B_r`) meets every `r`-local bottleneck in `B_r` of order `≤ k`. -/
theorem theorem_7_19 {V W : Type u} (G : SimpleGraph V) (hlf : IsLocallyFinite G)
    (hG : G.Connected) (r k : ℕ) (C : SimpleGraph W) (p : C →g G) (hp : IsLocalCovering G r p)
    (hΔ : DisplacementBound p r k) (hstar : 2 ≤ r ∨ k = 1) (Br : Set (Set (ULSep V)))
    (hBr : ∀ β ∈ Br, ∃ j, IsLocalBottleneck G r j β) :
    ∀ β ∈ Br, ∀ j ≤ k, IsLocalBottleneck G r j β → (β ∩ LNle G r Br k).Nonempty := by sorry

end LocalSepDecomp
