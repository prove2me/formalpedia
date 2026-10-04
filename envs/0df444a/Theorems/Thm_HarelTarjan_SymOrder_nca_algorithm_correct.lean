-- Prove2me | Theorems.Thm_HarelTarjan_SymOrder_nca_algorithm_correct
-- name    : HarelTarjan.SymOrder.nca_algorithm_correct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:49:52.127062+00:00
-- url     : https://prove2.me/theorems/bbd6532e-de66-4773-8da2-e6cf7b3db392
-- title:
--   The symmetric-order algorithm computes $\operatorname{nca}(v,w)$ in a complete binary tree
-- statement:
--   Let $T$ be the complete binary tree of depth $d$ whose vertices are numbered from $1$ to $n$ in symmetric order, $\mathrm{sym}(v)$ the number of $v$ and $h(v)$ its height. The algorithm of §3 (p. 342) computes $\operatorname{nca}(v,w)$ from the numbers alone:
--
--   1. **Step 1.** Compute $d_0$, the depth of $\operatorname{nca}(v,w)$, by the nca depth algorithm: $d_0 = d - h(v)$ if $\mathrm{sym}(w) \in [\mathrm{sym}(v) - 2^{h(v)} + 1, \mathrm{sym}(v) + 2^{h(v)} - 1]$; otherwise $d_0 = d - h(w)$ if $\mathrm{sym}(v) \in [\mathrm{sym}(w) - 2^{h(w)} + 1, \mathrm{sym}(w) + 2^{h(w)} - 1]$; otherwise $d_0 = d - \lfloor \lg(\mathrm{sym}(v) \oplus \mathrm{sym}(w)) \rfloor$.
--   2. **Step 2.** Compute the depth-$d_0$ ancestor of $v$ by the depth algorithm: with $h = d - d_0$, return $\mathrm{sym}^{-1}\left(2^{h+1} \lfloor \mathrm{sym}(v)/2^{h+1} \rfloor + 2^h\right)$.
--
--   The theorem: for all vertices $v, w$ of $T$, with $h = d - d_0$, the vertex $\operatorname{nca}(v,w)$ is the unique vertex with number $2^{h+1} \lfloor \mathrm{sym}(v)/2^{h+1} \rfloor + 2^h$, that is, for every vertex $u$,
--   $$\mathrm{sym}(u) = 2^{h+1} \left\lfloor \mathrm{sym}(v)/2^{h+1} \right\rfloor + 2^h \iff u = \operatorname{nca}(v,w),$$
--   so the algorithm returns $\operatorname{nca}(v,w)$.
--
--   This is the constant-time nearest common ancestor computation on complete binary trees that the paper's general algorithm reduces to.
--
--   **Formalization Note** $\lfloor \lg x \rfloor$ is `Nat.log 2 x` and $\oplus$ is `^^^` on $\mathbb N$; interval tests are written additively. The returned vertex $\mathrm{sym}^{-1}(N)$ is characterised as "a vertex has number $N$ if and only if it is $\operatorname{nca}(v,w)$", so no inverse function is defined. The $O(1)$ running time is not formalized.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 342, §3, Algorithm to compute nca(v, w) (unnumbered)

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym
import Definitions.Def_HarelTarjan_SymOrder_Algorithms

namespace HarelTarjan.SymOrder

/-- The algorithm to compute `nca(v, w)` (§3, p. 342) is correct. Step 1 computes
`d₀ = ncaDepthAlg v w`, the depth of `nca(v, w)` by the nca depth algorithm; Step 2 computes the
number `depthAlgNum v d₀` of the depth-`d₀` ancestor of `v` by the depth algorithm, and returns
`sym⁻¹` of it, the vertex with that number. The theorem states that the vertex with that number
exists, is unique, and is `nca(v, w)`: a vertex `u` has number `depthAlgNum v (ncaDepthAlg v w)`
if and only if `u = nca(v, w)`. So the algorithm returns `nca(v, w)` for all vertices `v`, `w`. -/
theorem nca_algorithm_correct {d : ℕ} (v w : Vertex d) :
    ∀ u : Vertex d, sym u = depthAlgNum v (ncaDepthAlg v w) ↔ u = nca v w := by sorry

end HarelTarjan.SymOrder
