-- Prove2me | Theorems.Thm_LocalSepDecomp_theorem_1_local_bottleneck_decomposition
-- name    : LocalSepDecomp.theorem_1_local_bottleneck_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:42.66581+00:00
-- url     : https://prove2.me/theorems/fa68ac65-99b9-4e31-9a28-b5e5c633595b
-- title:
--   Theorem 1 — the $r$-local bottleneck graph-decomposition $H^{\le k}_r(G)$
-- statement:
--   Let $G$ be a finite connected graph and $r,k\in\mathbb N$ with $k<K(G,r)$, where $K(G,r)=\Delta_r(G)/r+1$ for $r>0$ and $K(G,0)=2$. Let $H^{\le k}_r(G)=H(N^{\le k}_r(G))$, with $N^{\le k}_r(G)$ built from all $r$-local bottlenecks of order $\le k$. Then:
--
--   1. $H^{\le k}_r(G)$ is a canonical graph-decomposition of $G$ that represents all the $r$-local bottlenecks in $G$ of order $\le k$;
--   2. $H^{\le k}_r(G_r)$ is a canonical tangle tree-decomposition of scope $k$ of the $r$-local covering $G_r$;
--   3. $H^{\le k}_r(G)$ is canonically isomorphic, via the map $\tau$ of Theorem 8.21, to the graph-decomposition of $G$ obtained from $H^{\le k}_r(G_r)$ by folding via $p_r$;
--   4. $H^{\le k}_r(G)$ refines $H^{\le \ell}_r(G)$ for every $\ell\le k$: contracting in $H^{\le k}_r(G)$ the edges in $N^{\le k}_r(G)\setminus N^{\le\ell}_r(G)$ gives $H^{\le\ell}_r(G)$.
--
--   This is the paper's main result: a finite, local construction of the canonical graph-decomposition that [DJKK26] obtained by folding a tree of tangles of the infinite $r$-local covering.
--
--   Differences from the source:
--   - encoding: the r-local covering $p_r : G_r \to G$, unique up to isomorphism of coverings → an arbitrary covering $p : C \to G$ with `IsLocalCovering G r p` (characteristic subgroup = the r-local subgroup), on a vertex type in the universe of $V$; reason: the paper constructs $G_r$ only up to isomorphism; every statement holds for one such covering iff for all, and one exists in the universe of $V$ (walks modulo the r-local subgroup)
--   - encoding: $k<K(G,r)$ with $K(G,r)=\Delta_r(G)/r+1$ ($r>0$), $K(G,0)=2$ → $(k:\mathbb R_{\ge0}^\infty)<K$ with $K$ in $[0,\infty]$ (`Kval`); reason: $\Delta_r(G)=\infty$ gives $K=\infty$; same instances
--   - reading: $H^{\le k}_r(G)$ is canonically isomorphic to the folding of $H^{\le k}_r(G_r)$ → the isomorphism is the explicit map $\tau$ of Theorem 8.21 (cutouts to the cutouts projecting onto them, separations to their lifts), preserving parts; reason: §9 derives (iii) from Theorem 8.21, which names this isomorphism; it is defined from $G$, $r$, $k$ without choices
--   - generalization: $H^{\le k}_r(G)$ refines $H^{\le\ell}_r(G)$, i.e. $H^{\le\ell}_r(G)=H^{\le k}_r(G)/F$ for some edge set $F$ → $H^{\le\ell}_r(G)$ is isomorphic, with parts and by the identity on edges, to $H^{\le k}_r(G)/(N^{\le k}_r(G)\setminus N^{\le\ell}_r(G))$; reason: this is Lemma 8.23, by which §9 proves (iv); it specializes to the definition of refining with $F=N^{\le k}_r(G)\setminus N^{\le\ell}_r(G)$
--   - reading: tangles as in [D25, §12.5] → Diestel's tangles of every order $k\in\mathbb N$ (`IsTangle`); reason: the paper cites the definition without stating it
--   - reading: $s \succ t$ (used without a separate definition) and crossing/$\succcurlyeq$ defined for $r$-local separations with $r$-tomic separators → $s \succ t$ is $s \succcurlyeq t \wedge s \ne t$; the crossing and $\succcurlyeq$ conditions are defined for all pairs; reason: strict part of $\succcurlyeq$, as $>$ for $\geqslant$ in §8.1; the statement only applies them to separations with $r$-tomic separators
--   - encoding: orders $|X|$ of separators → `Set.encard` in $\mathbb N_\infty$; reason: separators of the infinite cover can be infinite (p.29); no finite instance changes
--   - encoding: nodes and edges of the folded decomposition are the $D(p_r)$-orbits of the nodes and edges of $H^{\le k}_r(G_r)$ (Construction 2.6) → classes of the relation 'related by a deck transformation' on cutouts and on separations, ends and parts computed from representatives (`foldedH`); reason: Construction 2.6 with the natural action of $D(p_r)$; the parts $p_r(G_t)$ are taken for $t\in h$ as on p.18
--   - reading: $\tau$ (Theorem 8.21) is defined on the cutouts of $N^{\le k}_r(G)$ → when $N^{\le k}_r(G)=\emptyset$ (e.g. $k=0$; no cutouts), $\tau$ sends the single node of $H(\emptyset)$ to the class of the single node of $H^{\le k}_r(G_r)=H(\emptyset)$; reason: both decompositions are then the trivial one-node decomposition with part $G$ (Construction 8.17)
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 1, p.6 (restated p.56)

import Mathlib
import Definitions.Def_LocalSepDecomp_Cutouts

set_option autoImplicit false

namespace LocalSepDecomp

open SimpleGraph

universe u

/-- **Theorem 1.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 1, p.6 (restated p.56).
Let `G` be a finite connected graph and `r, k ∈ ℕ` with `k < K(G, r)`.
(i) `H^{≤k}_r(G)` is a canonical graph-decomposition of `G` that represents all the `r`-local
bottlenecks in `G` of order `≤ k`.
(ii) `H^{≤k}_r(G_r)` is a canonical tangle tree-decomposition of scope `k` of the `r`-local
covering `G_r`.
(iii) `H^{≤k}_r(G)` is canonically isomorphic to the graph-decomposition of `G` obtained from the
canonical tree-decomposition `H^{≤k}_r(G_r)` of `G_r` by folding via `p_r`.
(iv) `H^{≤k}_r(G)` refines `H^{≤ℓ}_r(G)` for all `ℓ ∈ ℕ` with `ℓ ≤ k`.

**Formalization Note.** `G_r` is any `r`-local covering `p : C → G` (all are isomorphic), and
`K(G, r)` is computed from it (`Kval`, in `ℝ≥0∞`). "Canonical" is `Aut`-canonical (`Γ = ⊤`).
(iii): the canonical isomorphism is the map `τ` of Theorem 8.21∗ (`IsTauIso`). (iv): `H^{≤ℓ}_r(G)`
is isomorphic, with parts and by the identity on edges, to `H^{≤k}_r(G)` with the edges in
`N^{≤k}_r(G) ∖ N^{≤ℓ}_r(G)` contracted. -/
theorem theorem_1_local_bottleneck_decomposition {V W : Type u} [Finite V] (G : SimpleGraph V)
    (hG : G.Connected) (r k : ℕ) (C : SimpleGraph W) (p : C →g G) (hp : IsLocalCovering G r p)
    (hk : (k : ENNReal) < Kval p r) :
    (IsGraphDecomp (Hle G r k) ∧ IsCanonicalDecomp ⊤ (Hle G r k) ∧
        RepresentsLBottlenecks G r k (NleSec9 G r k)) ∧
      (IsTangleTreeDecomp C k (Hle C r k) ∧ IsCanonicalDecomp ⊤ (Hle C r k)) ∧
      (∃ ψ : DecompIso (Hle G r k) (foldedH p r (NleSec9 C r k)),
        IsTauIso p r (NleSec9 G r k) (NleSec9 C r k) ψ) ∧
      ∀ ℓ ≤ k, ∃ ψ : DecompIso (Hle G r ℓ)
          (contract (Hle G r k) {e | e.1 ∉ NleSec9 G r ℓ}),
        ∀ e, (ψ.edge e).1.1 = e.1 := by sorry

end LocalSepDecomp
