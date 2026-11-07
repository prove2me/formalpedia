-- Prove2me | Theorems.Thm_GenTuranHard_ineq_4_12_4_13
-- name    : GenTuranHard.ineq_4_12_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:57.59646+00:00
-- url     : https://prove2.me/theorems/7220b676-aefb-4f78-9209-bb47477a21db
-- title:
--   Inequalities (4.12)–(4.13) — $\mathrm{ex}'(Z) \ge L + S\,\mathrm{cut}_{k-1}(G) - a$ and $\mathrm{ex}(Z) \le L + S\,\mathrm{ex}(G,K_2,K_k) + b$
-- statement:
--   Let $T$ be a bipartite graph with $e(T) > 0$, $\mathcal F$ a family such that no member is a subgraph of a blow-up of $T$, $k = \min_{F \in \mathcal F} \chi(F)$ and $\gamma$ the number of automorphisms of $T$. There are constants $\eta = \eta(T, \mathcal F) > 0$ and $C = C(T, \mathcal F) > 0$ such that for every graph $G$ on $n \ge 1$ vertices and every positive integer $B$, with $\mathbf x$ as in (4.3) and $Z = L_{\mathbf x}(G)(B)$,
--
--   $$
--   \mathrm{ex}'(Z, T, \mathcal F) \ge \gamma^{-1} B^{v(T)} \big( A_0(\mathbf x, G) + S(\mathbf x, n)\cdot \mathrm{cut}_{k-1}(G) \big) - \gamma^{-1} v(T)^2\, v(Z)^{v(T)-1}, \tag{4.12}
--   $$
--
--   $$
--   \mathrm{ex}(Z, T, \mathcal F) \le \gamma^{-1} B^{v(T)} \Big( A_0(\mathbf x, G) + S(\mathbf x, n)\cdot \mathrm{ex}(G, K_2, K_k) + S(\mathbf x, n)\, C\big(n^{k-\eta} B^{-\eta} + n^{-3}\big) \Big). \tag{4.13}
--   $$
--
--   On $\mathcal G_k$ both $\mathrm{cut}_{k-1}(G)$ and $\mathrm{ex}(G, K_2, K_k)$ equal $z$ (Lemma 3.4), and the two bounds are the estimate (2.1) with $L$, $S$, $a$, $b$ as defined on p.21; Corollary 3.3 then gives Theorem 1.5.
--
--   **Formalization Note** $\eta$ and $C$ are chosen before $G$ and $B$; $B$ is not yet fixed to $n^\beta$ (that is the choice (4.14) of the final step). Real powers are `Real.rpow`.
--
--   Differences from the source:
--   - generalization: G ∈ 𝒢_k and z = cut_{k−1}(G) in both bounds → every G with n ≥ 1; z = cut_{k−1}(G) in (4.12) and z = ex(G, K₂, K_k) in (4.13); reason: (4.12) uses only a (k−1)-colorable spanning H with e(H) = cut_{k−1}(G), (4.13) only Lemma 4.8 in its general form; on 𝒢_k both values are z by (4.9)
--   - encoding: k = min_{F∈𝓕} χ(F) → hypotheses: no member of 𝓕 is (k−1)-colorable, and some member is k-colorable; reason: these two conditions say exactly that the least chromatic number in 𝓕 is k (χ(F) ≤ r iff F is r-colorable)
--   - encoding: ex and ex′ as maxima over (spanning) 𝓕-free subgraphs H ⊆ G → Finset.sup over G.Subgraph (with H.verts = univ for ex′); reason: a finite maximum in ℕ; the empty subgraph is 𝓕-free whenever no member of 𝓕 is empty
--   - encoding: N(H, T), the number of copies of T in H → Mathlib copyCount: subgraphs of H isomorphic to T; reason: the same count: copies with different vertex sets or edge sets are different subgraphs
--   - encoding: Z = L_x(G)(B), its clusters C_v → Zgraph x G B on Fin (v(L_x(G))·B), vertex i in the cluster of vertex i / B; reason: one numbering of the B-blow-up; every quantity involved is isomorphism-invariant
--   - encoding: sums over Q ∈ 𝒬_T of f_Q(x)·(…) with f_Q a sum over sequences with T_s ≅ Q → sums directly over the sequences of (4.1), grouped by p(T_s); reason: regrouping a finite sum; hom(·,G), v(·), p(·) are isomorphism-invariant, so the values are equal
--   - generalization: v(T) ≥ 3 (the standing assumption of §4, p.12) → every bipartite T with e(T) > 0 (v(T) ≥ 2, s = v(T) − 2 ≥ 0); reason: for v(T) = 2 the construction is L_x(G) = G with the empty sequence; the source's case v(T) ≥ 3 is included
--   - reading: the displayed chains (4.12) and (4.13), whose middle terms involve the H and J chosen on p.21 → their outer inequalities: the lower bound on ex′(Z, T, 𝓕) and the upper bound on ex(Z, T, 𝓕); reason: the middle links are (4.11), Lemma 4.8 and Lemma 4.9 applied to graphs constructed in the proof (separate items); the outer bounds are what (2.1) and the proof of Theorem 1.5 use
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Inequalities (4.12) and (4.13), p.21

import Mathlib
import Definitions.Def_GenTuranHard_A0
import Definitions.Def_GenTuranHard_Zgraph
import Definitions.Def_GenTuranHard_exT
import Definitions.Def_GenTuranHard_cutR

set_option autoImplicit false

namespace GenTuranHard

/-- **Inequalities (4.12) and (4.13)** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…,
(4.12)–(4.13), p.21): the sandwich (2.1) for `Z = L_x(G)(B)`. Let `T` be bipartite with `e(T) > 0`, `𝓕`
a family no member of which is a subgraph of a blow-up of `T`, `k = min_{F ∈ 𝓕} χ(F)`, `γ = |Aut T|`,
`x` as in (4.3) and `n = v(G)`. Then there are `η = η(T, 𝓕) > 0` and `C = C(T, 𝓕) > 0` such that
`ex′(Z, T, 𝓕) ≥ γ⁻¹B^{v(T)}(A₀(x, G) + S(x, n)·z) − γ⁻¹v(T)²v(Z)^{v(T)−1}` and
`ex(Z, T, 𝓕) ≤ γ⁻¹B^{v(T)}(A₀(x, G) + S(x, n)·z + S(x, n)·C(n^{k−η}B^{−η} + n^{−3}))`.

**Formalization Note** In the paper `G ∈ 𝒢_k` and `z = cut_{k−1}(G)` in both bounds. Here `G` is any
graph with `n ≥ 1`, the lower bound has `z = cut_{k−1}(G)` and the upper bound `z = ex(G, K₂, K_k)`; on
`𝒢_k` the two agree by Lemma 3.4 (that is (4.9)). `η, C` are chosen before `G` and `B ≥ 1`; `B` is not
fixed to `n^β` here. `k` is encoded by `hkF` and `hkF'`. -/
theorem ineq_4_12_4_13 {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W)
    (hT : T.IsBipartite) (hTe : T.edgeSet.Nonempty) (Fam : Set FinGraph)
    (hF : ∀ F ∈ Fam, ¬ InBlowUp F.2 T)
    (k : ℕ) (hkF : ∀ F ∈ Fam, ¬ F.2.Colorable (k - 1)) (hkF' : ∃ F ∈ Fam, F.2.Colorable k) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (G : FinGraph) (B : ℕ), 1 ≤ G.1 → 1 ≤ B →
      ((Nat.card (T ≃g T) : ℝ)⁻¹ * (B : ℝ) ^ Fintype.card W *
          ((A0 T (xVec (Fintype.card W) G.1) G : ℝ) +
            (Sx T (xVec (Fintype.card W) G.1) G.1 : ℝ) * (cutR (k - 1) G.2 : ℝ)) -
        (Nat.card (T ≃g T) : ℝ)⁻¹ * (Fintype.card W : ℝ) ^ 2 *
          ((Zgraph (xVec (Fintype.card W) G.1) G B).1 : ℝ) ^ (Fintype.card W - 1) ≤
        (exSpan (Zgraph (xVec (Fintype.card W) G.1) G B).2 T Fam : ℝ)) ∧
      ((exT (Zgraph (xVec (Fintype.card W) G.1) G B).2 T Fam : ℝ) ≤
        (Nat.card (T ≃g T) : ℝ)⁻¹ * (B : ℝ) ^ Fintype.card W *
          ((A0 T (xVec (Fintype.card W) G.1) G : ℝ) +
            (Sx T (xVec (Fintype.card W) G.1) G.1 : ℝ) *
              (exT G.2 (⊤ : SimpleGraph (Fin 2)) {cliqueFG k} : ℝ) +
            (Sx T (xVec (Fintype.card W) G.1) G.1 : ℝ) *
              (C * ((G.1 : ℝ) ^ ((k : ℝ) - η) * (B : ℝ) ^ (-η) + (G.1 : ℝ) ^ (-3 : ℤ))))) := by sorry

end GenTuranHard
