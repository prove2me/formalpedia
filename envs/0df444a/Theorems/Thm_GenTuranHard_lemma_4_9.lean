-- Prove2me | Theorems.Thm_GenTuranHard_lemma_4_9
-- name    : GenTuranHard.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:08.295481+00:00
-- url     : https://prove2.me/theorems/289f718a-7359-459c-a5c0-9905d1155fb6
-- title:
--   Lemma 4.9 — $\hom(T, L_{\mathbf x}(H)(B)) \ge B^{v(T)}(A_0(\mathbf x,H) + S(\mathbf x,n)\,e(H))$
-- statement:
--   Let $T$ be a bipartite graph with $e(T) > 0$. For every $n$-vertex graph $H$ and every positive integer $B$, with $\mathbf x$ as in (4.3),
--
--   $$
--   \hom(T, L_{\mathbf x}(H)(B)) \ge B^{v(T)} \Big( A_0(\mathbf x, H) + S(\mathbf x, n)\cdot e(H) \Big).
--   $$
--
--   Applied to a largest $(k-1)$-colorable spanning subgraph $H$ of $G$, this gives the lower half of the sandwich (2.1).
--
--   Differences from the source:
--   - encoding: Z = L_x(G)(B), its clusters C_v → Zgraph x G B on Fin (v(L_x(G))·B), vertex i in the cluster of vertex i / B; reason: one numbering of the B-blow-up; every quantity involved is isomorphism-invariant
--   - encoding: sums over Q ∈ 𝒬_T of f_Q(x)·(…) with f_Q a sum over sequences with T_s ≅ Q → sums directly over the sequences of (4.1), grouped by p(T_s); reason: regrouping a finite sum; hom(·,G), v(·), p(·) are isomorphism-invariant, so the values are equal
--   - generalization: v(T) ≥ 3 (the standing assumption of §4, p.12) → every bipartite T with e(T) > 0 (v(T) ≥ 2, s = v(T) − 2 ≥ 0); reason: for v(T) = 2 the construction is L_x(G) = G with the empty sequence; the source's case v(T) ≥ 3 is included
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Lemma 4.9, p.20

import Mathlib
import Definitions.Def_GenTuranHard_A0
import Definitions.Def_GenTuranHard_Zgraph

set_option autoImplicit false

namespace GenTuranHard

/-- **Lemma 4.9** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Lemma 4.9, p.20). For
every `n`-vertex graph `H` and every positive integer `B`, with `x` as in (4.3),
`hom(T, L_x(H)(B)) ≥ B^{v(T)} (A₀(x, H) + S(x, n)·e(H))`.

**Formalization Note** `T` is the §4 graph (bipartite, `e(T) > 0`). `L_x(H)(B)` is `Zgraph x H B`. -/
theorem lemma_4_9 {W : Type} [Fintype W] (T : SimpleGraph W) (hT : T.IsBipartite)
    (hTe : T.edgeSet.Nonempty) (H : FinGraph) (B : ℕ) (hB : 1 ≤ B) :
    B ^ Fintype.card W * (A0 T (xVec (Fintype.card W) H.1) H +
        Sx T (xVec (Fintype.card W) H.1) H.1 * edgeCount H.2) ≤
      homCount T (Zgraph (xVec (Fintype.card W) H.1) H B).2 := by sorry

end GenTuranHard
