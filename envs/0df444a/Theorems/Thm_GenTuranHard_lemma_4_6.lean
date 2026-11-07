-- Prove2me | Theorems.Thm_GenTuranHard_lemma_4_6
-- name    : GenTuranHard.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:41.227973+00:00
-- url     : https://prove2.me/theorems/e0ff6a5d-8c55-4e2a-a54d-1a03aa941b78
-- title:
--   Lemma 4.6 — $A_0 = \sum f_Q(\mathbf x) n^{v(Q)}$, $A_2 = S(\mathbf x,n)\, e(G)$, $A_{\ge3} = S(\mathbf x,n)\, O_T(n^{-3})$
-- statement:
--   Let $T$ be a bipartite graph with $e(T) > 0$ and $G$ a graph on $n$ vertices, and let $\mathbf x$ be defined as in (4.3). Then
--
--   $$
--   A_0(\mathbf x, G) = \sum_{Q \in \mathcal Q_T,\ p(Q) = 0} f_Q(\mathbf x)\, n^{v(Q)}, \qquad A_2(\mathbf x, G) = S(\mathbf x, n)\cdot e(G), \qquad A_{\ge 3}(\mathbf x, G) = S(\mathbf x, n)\cdot O_T(n^{-3}).
--   $$
--
--   The first two parts depend on $G$ only through $n$ and $e(G)$; the third says that the terms with at least three nonisolated vertices are negligible compared with $S(\mathbf x, n)$.
--
--   **Formalization Note** $T$ is the graph fixed in §4 (bipartite, $e(T) > 0$). The first sum is over the sequences of (4.1) with $p(T_s) = 0$. $O_T(n^{-3})$ is an explicit constant $C > 0$ depending only on $T$, chosen before $G$, with $A_{\ge 3}(\mathbf x, G) \le C\, S(\mathbf x, n)\, n^{-3}$ for every $G$ with $n \ge 1$; $A_{\ge 3} \ge 0$, so this is the whole content.
--
--   Differences from the source:
--   - encoding: sums over Q ∈ 𝒬_T of f_Q(x)·(…) with f_Q a sum over sequences with T_s ≅ Q → sums directly over the sequences of (4.1), grouped by p(T_s); reason: regrouping a finite sum; hom(·,G), v(·), p(·) are isomorphism-invariant, so the values are equal
--   - generalization: O_T(n^{−3}) (|h(n)| ≤ C f(n) for n ≥ n_T, p.5) → an explicit C > 0 depending only on T, chosen before G, with the bound for every n ≥ 1; reason: n_T = 1 is a special choice of the threshold; the bound is a nonnegative quantity, so the absolute value is not needed
--   - generalization: v(T) ≥ 3 (the standing assumption of §4, p.12) → every bipartite T with e(T) > 0 (v(T) ≥ 2, s = v(T) − 2 ≥ 0); reason: for v(T) = 2 the construction is L_x(G) = G with the empty sequence; the source's case v(T) ≥ 3 is included
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Lemma 4.6, p.16 (proof pp.16–17)

import Mathlib
import Definitions.Def_GenTuranHard_A0

set_option autoImplicit false

namespace GenTuranHard

open scoped Classical in
/-- **Lemma 4.6** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Lemma 4.6, p.16). For any
graph `G` on `n` vertices and bipartite graph `T`, with `x` defined as in (4.3),
`A₀(x, G) = Σ_{Q ∈ 𝒬_T, p(Q) = 0} f_Q(x) n^{v(Q)}`, `A₂(x, G) = S(x, n)·e(G)` and
`A_{≥3}(x, G) = S(x, n)·O_T(n^{−3})`.

**Formalization Note** `T` is the §4 graph (bipartite, `e(T) > 0`, p.12). The first sum is taken over
the sequences of (4.1) with `p(T_s) = 0`, as in `A0`. `O_T(n^{−3})` is an explicit constant `C > 0`
depending only on `T`, chosen before `G`, with `A_{≥3}(x, G) ≤ C·S(x, n)·n^{−3}` for every `G` with
`n ≥ 1` (`A_{≥3} ≥ 0`, so the upper bound is the whole content). -/
theorem lemma_4_6 {W : Type} [Fintype W] (T : SimpleGraph W) (hT : T.IsBipartite)
    (hTe : T.edgeSet.Nonempty) :
    (∀ G : FinGraph, A0 T (xVec (Fintype.card W) G.1) G =
      ∑ Is ∈ (validSeqs (xVec (Fintype.card W) G.1).length (toFin T)).filter
          (fun Is => pNon (termGraph (toFin T) Is) = 0),
        monoWeight (xVec (Fintype.card W) G.1) Is * G.1 ^ (termGraph (toFin T) Is).1) ∧
      (∀ G : FinGraph, A2 T (xVec (Fintype.card W) G.1) G =
        Sx T (xVec (Fintype.card W) G.1) G.1 * edgeCount G.2) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ G : FinGraph, 1 ≤ G.1 →
        (Ages3 T (xVec (Fintype.card W) G.1) G : ℝ) ≤
          C * (Sx T (xVec (Fintype.card W) G.1) G.1 : ℝ) * (G.1 : ℝ) ^ (-3 : ℤ) := by sorry

end GenTuranHard
