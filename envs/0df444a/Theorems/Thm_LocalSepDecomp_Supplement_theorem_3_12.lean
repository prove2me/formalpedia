-- Prove2me | Theorems.Thm_LocalSepDecomp_Supplement_theorem_3_12
-- name    : LocalSepDecomp.Supplement.theorem_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:47:29.371278+00:00
-- url     : https://prove2.me/theorems/e0c5d012-477d-406d-9340-836b4d8a5939
-- title:
--   Theorem 3.12 — $N^{\le k}(G)$ is a canonical tree of tangles of scope $k$, and $T(N^{\le k}(G))$ a canonical tangle tree-decomposition
-- statement:
--   Let $G$ be a locally finite, connected graph (not necessarily finite), and let $k\in\mathbb N$. Then $N^{\le k}(G)$ is a canonical tree of tangles of $G$ of scope $k$. Moreover, $T(N^{\le k}(G))$ is a canonical tangle tree-decomposition of $G$ of scope $k$.
--
--   Here $N^{\le k}(G)=N^{<k}(G)\cup N^k(G)$ is built by Construction 3.6 from the set of all bottlenecks of $G$, and $T(N)$ is the candidate of Construction 2.3. A **tree of tangles of scope $k$** is a nested set of separations containing, for every two $(\le k)$-distinguishable tangles of $G$, a separation that distinguishes them efficiently; a **tangle tree-decomposition of scope $k$** is a tree-decomposition whose induced separations form a tree of tangles of scope $k$. Canonical means invariant under $\mathrm{Aut}(G)$.
--
--   $$\text{$N^{\le k}(G)$ is an $\mathrm{Aut}(G)$-invariant tree of tangles of scope $k$, and $T(N^{\le k}(G))$ an $\mathrm{Aut}(G)$-canonical tangle tree-decomposition of scope $k$.}$$
--
--   This is the global, possibly infinite, instance of the bottleneck method that the paper transfers to $r$-local separations.
--
--   **Formalization Note** The conclusion also states that every orientation of every separation in $N^{\le k}(G)$ lies in a splitting star, which is what makes $T(N^{\le k}(G))$ defined (p.17).
--
--   Differences from the source:
--
--   - reading: T(N^{≤k}(G)) is a (canonical tangle) tree-decomposition → every element of ori(N^{≤k}(G)) lies in a splitting star (AllOriInSplittingStars), and Tdecomp G (N^{≤k}(G)) is a tangle tree-decomposition of scope k and Aut(G)-canonical; reason: T(N) of Construction 2.3 is defined only when every orientation lies in a splitting star (p.17); the claim that T(N) is a tree-decomposition presupposes it, so it is asserted (the stronger reading)
--   - encoding: N^{≤k}(G) (no set B named) → Nle G k = Nlt ∪ Nk of Construction 3.6 with B the set of all bottlenecks of G (allBottlenecks); reason: p.21: without reference to B, B is the set of all bottlenecks; p.12: N^{≤k} := N^{<k} ∪ N^k
--   - encoding: canonical (tree of tangles; tree-decomposition) → IsCanonicalUSepSet G ⊤ and IsCanonicalDecomp ⊤; reason: canonical means Aut(G)-canonical (pp.14, 17)
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), Theorem 3.12, p.23

import Mathlib
import Definitions.Def_LocalSepDecomp_Supplement_TreeFromNested

set_option autoImplicit false

namespace LocalSepDecomp.Supplement

open SimpleGraph

universe u

/-- **Theorem 3.12.** R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via
Local Separations*, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…),
Theorem 3.12, p.23. Let `G` be a locally finite, connected graph, and let `k ∈ ℕ`. Then
`N^{≤k}(G)` is a canonical tree of tangles of `G` of scope `k`. Moreover, `T(N^{≤k}(G))` is a
canonical tangle tree-decomposition of `G` of scope `k`.

**Formalization Note.** `N^{≤k}(G) = N^{<k}(G) ∪ N^k(G)` for the set of all bottlenecks of `G`
(`Nle`). `G` may be infinite (no finiteness assumption). "Canonical" is `Aut(G)`-canonical
(`Γ = ⊤`) for the set and for the decomposition. Since `T(N)` of Construction 2.3 is only defined
when every element of `ori(N)` lies in a splitting star (p.17), that is asserted as part of the
conclusion (`AllOriInSplittingStars`). -/
theorem theorem_3_12 {V : Type u} (G : SimpleGraph V) (hlf : IsLocallyFinite G)
    (hG : G.Connected) (k : ℕ) :
    (IsTreeOfTangles G k (Nle G k) ∧ IsCanonicalUSepSet G ⊤ (Nle G k)) ∧
      (AllOriInSplittingStars G (Nle G k) ∧ IsTangleTreeDecomp G k (Tdecomp G (Nle G k)) ∧
        IsCanonicalDecomp ⊤ (Tdecomp G (Nle G k))) := by sorry

end LocalSepDecomp.Supplement
