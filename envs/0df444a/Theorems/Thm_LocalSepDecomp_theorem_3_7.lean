-- Prove2me | Theorems.Thm_LocalSepDecomp_theorem_3_7
-- name    : LocalSepDecomp.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:05.400211+00:00
-- url     : https://prove2.me/theorems/f14a4c48-eb57-493d-b8d8-ce7bdcadb382
-- title:
--   Theorem 3.7 — the nested set $N(G)$ built from bottlenecks
-- statement:
--   Let $G$ be a locally finite, connected graph and $\mathcal B$ any set of bottlenecks in $G$, and let $N^k(G,\beta)$, $N^k(G)$, $N^{<k}(G)$ and $N(G)$ be the sets of Construction 3.6 for $\mathcal B$. Then:
--
--   1. the sets are well-defined: every crossing number $x_k(s)$, $s\in S_k$, is finite;
--   2. $N(G)$ and every $N^{<k}(G)$ are nested;
--   3. $N^k(G,\beta)\neq\emptyset$ for every $k$ and every $k$-bottleneck $\beta$ in $G$;
--   4. if $\mathcal B$ is $\Gamma$-invariant for a subgroup $\Gamma\le\operatorname{Aut}(G)$, then $N(G)$ and every $N^{<k}(G)$ are $\Gamma$-canonical.
--
--   This is the global tree-of-bottlenecks theorem; its $r$-local analogue (Correspondence 7.17, Theorem 7.18) is what Theorem 1 is built on.
--
--   Differences from the source:
--   - reading: the sets $N^k$ are well-defined → every crossing number $x_k(s)$ on which they depend is finite; reason: Construction 3.6/7.16 counts crossings 'assuming for now that this number is finite'; the count is a cardinal in $\mathbb N_\infty$
--   - generalization: $N^k(G,\beta)$ (defined in Construction 3.6 for $\beta\in\mathcal B^k(G)$) non-empty for every $k$-bottleneck $\beta$ in $G$ → the same formula ($\beta$'s elements nested with $N^{<k}(G)$ of minimal $x_k$) is non-empty for every $k$-bottleneck $\beta$ of $G$, in $\mathcal B$ or not; reason: the printed clause quantifies over every $k$-bottleneck in $G$; Lemma 3.10's argument uses only that $\beta$ is a $k$-bottleneck and $N^{<k}(G)$ is nested; it specializes to $\beta\in\mathcal B^k(G)$
--   - encoding: orders $|X|$ of separators → `Set.encard` in $\mathbb N_\infty$; reason: separators of the infinite cover can be infinite (p.29); no finite instance changes
--   - encoding: $G$ locally finite → every neighbour set is finite (a `Prop`, not Mathlib's data-carrying `LocallyFinite` class); reason: same graphs
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 3.7, p.21

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts

set_option autoImplicit false

namespace LocalSepDecomp

open SimpleGraph

universe u

/-- **Theorem 3.7.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 3.7, p.21.
Let `G` be a locally finite, connected graph and `B` any set of bottlenecks in `G`. Then the sets
`N(G)` and `N^{<k}(G)` of Construction 3.6 are well-defined (every crossing number `x_k(s)`,
`s ∈ S_k`, is finite) and nested, and `N^k(G, β)` is non-empty for every `k` and every
`k`-bottleneck `β` in `G`. Moreover, if `B` is `Γ`-invariant for a subgroup `Γ ≤ Aut(G)`, then
`N(G)` and `N^{<k}(G)` are `Γ`-canonical.

**Formalization Note.** The paper defines `N^k(G, β)` for `β ∈ B^k(G)`; `NkAt G B k β` is the same
formula (elements of `β` nested with `N^{<k}(G)` with minimal `x_k`) for every `β`, and the
non-emptiness clause is stated, as printed, for every `k`-bottleneck `β` of `G`. It specializes to
`β ∈ B^k(G)` (Lemma 3.10, p.22). -/
theorem theorem_3_7 {V : Type u} (G : SimpleGraph V) (hlf : IsLocallyFinite G)
    (hG : G.Connected) (B : Set (Set (Sym2 (Set V)))) (hB : ∀ β ∈ B, ∃ k, IsBottleneck G k β) :
    (∀ k, ∀ s ∈ ⋃₀ globalBk G B k, xk G B k s < ⊤) ∧
      USepSetNested (Nall G B) ∧ (∀ k, USepSetNested (Nlt G B k)) ∧
      (∀ k, ∀ β, IsBottleneck G k β → (NkAt G B k β).Nonempty) ∧
      ∀ Γ : Subgroup (G ≃g G), IsInvariantBottleneckSet G Γ B →
        IsCanonicalUSepSet G Γ (Nall G B) ∧ ∀ k, IsCanonicalUSepSet G Γ (Nlt G B k) := by sorry

end LocalSepDecomp
