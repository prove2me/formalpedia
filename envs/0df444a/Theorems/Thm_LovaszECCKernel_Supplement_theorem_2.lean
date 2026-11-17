-- Prove2me | Theorems.Thm_LovaszECCKernel_Supplement_theorem_2
-- name    : LovaszECCKernel.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:11:33.781205+00:00
-- url     : https://prove2.me/theorems/5c8834da-3020-47de-baaa-198db92bad31
-- title:
--   Theorem 2 (Erdős–Goodman–Pósa Bound) — $\mathrm{ecp}(G)\le\lfloor n^2/4\rfloor$
-- statement:
--   **Theorem 2 (Erdős–Goodman–Pósa bound).** For every finite simple graph $G$ on $n$ vertices,
--   $$\mathrm{ecp}(G)\ \le\ \Big\lfloor\frac{n^2}{4}\Big\rfloor ,$$
--   that is, the edges of $G$ can be partitioned into at most $\lfloor n^2/4\rfloor$ cliques.
--
--   The bound is sharp: the balanced complete bipartite graph $K_{\lfloor n/2\rfloor,\lceil n/2\rceil}$ is triangle-free with $\lfloor n^2/4\rfloor$ edges, so it needs that many cliques. This bound is the baseline below which the paper's Theorems 4 and 6 measure the parameter $k$.
--
--   **Formalization Note** $G$ is a simple graph on any finite vertex type with $n$ elements, $n=0$ included; $\lfloor n^2/4\rfloor$ is integer division.
--
--   Differences from the source:
--   - encoding: an n-vertex graph G → a simple graph on a finite type V with n = |V|; reason: the same graphs, n = 0 included
--   - encoding: ⌊n²/4⌋ → the natural-number division n ^ 2 / 4; reason: equal for every n
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 2 (from [EGP66]), p.4 (= PDF p.4); construction and proof outline recalled on p.44

import Mathlib
import Definitions.Def_LovaszECCKernel_Supplement_ecp

set_option autoImplicit false

namespace LovaszECCKernel.Supplement

/-- **Theorem 2 (Erdős–Goodman–Pósa Bound [EGP66])** (Fomin, Golovach, Khargeliia, Sagunov, Simonov,
*Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa
Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), Theorem 2, p.4 (= PDF p.4); proof
outline recalled on p.44): "Edges of an n-vertex graph G can be partitioned in at most ⌊n²/4⌋
cliques."

**Formalization Note** `G` is any simple graph on a finite type `V` with `n = |V|` (`n = 0` included);
`⌊n²/4⌋` is the natural-number division `n ^ 2 / 4`; `ecp` is the minimum size of an edge clique
partition. -/
theorem theorem_2 {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ecp G ≤ Fintype.card V ^ 2 / 4 := by sorry

end LovaszECCKernel.Supplement
