-- Prove2me | Theorems.Thm_GenTuranHard_lemma_4_7
-- name    : GenTuranHard.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:53.137934+00:00
-- url     : https://prove2.me/theorems/2077fbfc-bb18-4666-a588-219bb8b736b0
-- title:
--   Lemma 4.7 — random transversal: $\hom(T,J) \le B^{v(T)}(A_0 + S\,\mathbb E[e(R_J)] + S\,O_T(n^{-3}))$
-- statement:
--   Let $T$ be a bipartite graph with $e(T) > 0$, $G$ a graph on $n \ge 1$ vertices, $B$ a positive integer, $\mathbf x$ as in (4.3) and $Z = L_{\mathbf x}(G)(B)$. For any graph $J \subseteq Z$,
--
--   $$
--   \hom(T, J) \le B^{v(T)} \Big( A_0(\mathbf x, G) + S(\mathbf x, n)\cdot \mathbb E[e(R_J)] + S(\mathbf x, n)\cdot O_T(n^{-3}) \Big),
--   $$
--
--   where $R_J$ is the graph of a uniformly random transversal of the clusters of $V(G)$.
--
--   This reduces the upper bound on homomorphisms into a subgraph of $Z$ to the expected number of edges of a random spanning subgraph of $G$.
--
--   **Formalization Note** $O_T(n^{-3})$ is $C n^{-3}$ with one constant $C > 0$ depending only on $T$, chosen before $G$, $B$ and $J$. The expectation is the average over all $B^n$ transversals.
--
--   Differences from the source:
--   - generalization: O_T(n^{−3}) (|h(n)| ≤ C f(n) for n ≥ n_T, p.5) → an explicit C > 0 depending only on T, chosen before G, with the bound for every n ≥ 1; reason: n_T = 1 is a special choice of the threshold; the bound is a nonnegative quantity, so the absolute value is not needed
--   - encoding: E[e(R_J)] over the uniform random transversal → avgEdges: the average of e(R_J) over all B^n choices σ : V(G) → Fin B; reason: the uniform distribution on a finite set; the expectation is this average
--   - encoding: Z = L_x(G)(B), its clusters C_v → Zgraph x G B on Fin (v(L_x(G))·B), vertex i in the cluster of vertex i / B; reason: one numbering of the B-blow-up; every quantity involved is isomorphism-invariant
--   - encoding: hom(T, J) for a subgraph J ⊆ Z → homCount T J.coe (homomorphisms into J as a graph on V(J)); reason: the same count: isolated vertices of T are mapped to vertices of J
--   - encoding: sums over Q ∈ 𝒬_T of f_Q(x)·(…) with f_Q a sum over sequences with T_s ≅ Q → sums directly over the sequences of (4.1), grouped by p(T_s); reason: regrouping a finite sum; hom(·,G), v(·), p(·) are isomorphism-invariant, so the values are equal
--   - generalization: v(T) ≥ 3 (the standing assumption of §4, p.12) → every bipartite T with e(T) > 0 (v(T) ≥ 2, s = v(T) − 2 ≥ 0); reason: for v(T) = 2 the construction is L_x(G) = G with the empty sequence; the source's case v(T) ≥ 3 is included
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Lemma 4.7, p.18 (proof pp.18–20)

import Mathlib
import Definitions.Def_GenTuranHard_A0
import Definitions.Def_GenTuranHard_Zgraph

set_option autoImplicit false

namespace GenTuranHard

/-- **Lemma 4.7** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Lemma 4.7, p.18). For any
graph `J ⊆ Z = L_x(G)(B)`, with `x` as in (4.3),
`hom(T, J) ≤ B^{v(T)} (A₀(x, G) + S(x, n)·E[e(R_J)] + S(x, n)·O_T(n^{−3}))`.

**Formalization Note** `T` is the §4 graph (bipartite, `e(T) > 0`). `O_T(n^{−3})` is `C·n^{−3}` with one
constant `C > 0` depending only on `T`, chosen before `G`, `B` and `J`; `n = v(G) ≥ 1` and `B ≥ 1`
(p.12, p.17). `E[e(R_J)]` is `avgEdges`, the average of `e(R_J)` over all `B^n` transversals.
`hom(T, J)` counts homomorphisms into `J` as a graph on its own vertex set `V(J)`. -/
theorem lemma_4_7 {W : Type} [Fintype W] (T : SimpleGraph W) (hT : T.IsBipartite)
    (hTe : T.edgeSet.Nonempty) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : FinGraph) (B : ℕ), 1 ≤ G.1 → 1 ≤ B →
      ∀ J : (Zgraph (xVec (Fintype.card W) G.1) G B).2.Subgraph,
        (homCount T J.coe : ℝ) ≤ (B : ℝ) ^ Fintype.card W *
          ((A0 T (xVec (Fintype.card W) G.1) G : ℝ) +
            (Sx T (xVec (Fintype.card W) G.1) G.1 : ℝ) *
              avgEdges (xVec (Fintype.card W) G.1) G B J +
            (Sx T (xVec (Fintype.card W) G.1) G.1 : ℝ) * (C * (G.1 : ℝ) ^ (-3 : ℤ))) := by sorry

end GenTuranHard
