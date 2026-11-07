-- Prove2me | Theorems.Thm_GenTuranHard_lemma_4_8
-- name    : GenTuranHard.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:53.555347+00:00
-- url     : https://prove2.me/theorems/809f8fd5-3e63-4021-949c-27255e31b0d8
-- title:
--   Lemma 4.8 — for $\mathcal F$-free $J \subseteq Z$: $\hom(T,J) \le B^{v(T)}(A_0 + S z + S\,O(n^{k-\eta}B^{-\eta} + n^{-3}))$
-- statement:
--   Let $T$ be a bipartite graph with $e(T) > 0$, $\mathcal F$ a family such that no member is a subgraph of a blow-up of $T$, and $k = \min_{F \in \mathcal F} \chi(F)$. There is a constant $\eta = \eta(T, \mathcal F) > 0$ such that for every graph $G$ on $n \ge 1$ vertices, every positive integer $B$, with $\mathbf x$ as in (4.3) and $Z = L_{\mathbf x}(G)(B)$, every $\mathcal F$-free subgraph $J \subseteq Z$ satisfies
--
--   $$
--   \hom(T, J) \le B^{v(T)} \Big( A_0(\mathbf x, G) + S(\mathbf x, n)\cdot z + S(\mathbf x, n)\cdot O\big(n^{k-\eta} B^{-\eta} + n^{-3}\big) \Big),
--   $$
--
--   where $z = \mathrm{ex}(G, K_2, K_k)$.
--
--   This is the upper half of the sandwich (2.1): an $\mathcal F$-free subgraph of $Z$ cannot have many more homomorphic images of $T$ than the construction from a largest $K_k$-free subgraph of $G$.
--
--   **Formalization Note** The paper states the lemma for $G \in \mathcal G_k$ with $z = \mathrm{cut}_{k-1}(G)$, which equals $\mathrm{ex}(G, K_2, K_k)$ on $\mathcal G_k$ by (4.9). The constant of $O(\cdot)$ is an explicit $C > 0$; $\eta$ and $C$ depend only on $T$ and $\mathcal F$ and are chosen before $G$, $B$ and $J$.
--
--   Differences from the source:
--   - generalization: T, 𝓕 fixed for the section; G ∈ 𝒢_k with z = cut_{k−1}(G) → every graph G with n ≥ 1 and z = ex(G, K₂, K_k); reason: the proof uses only (4.10), valid for every G; on 𝒢_k, ex(G, K₂, K_k) = cut_{k−1}(G) by (4.9)
--   - encoding: k = min_{F∈𝓕} χ(F) → hypotheses: no member of 𝓕 is (k−1)-colorable, and some member is k-colorable; reason: these two conditions say exactly that the least chromatic number in 𝓕 is k (χ(F) ≤ r iff F is r-colorable)
--   - encoding: O(n^{k−η}B^{−η} + n^{−3}) with implicit constant depending on T, F → C·(n^{k−η}·B^{−η} + n^{−3}) with C > 0 chosen with η before G, B, J; Real.rpow; reason: the definition of O(·) (p.5) for this quantity, with the threshold n ≥ 1
--   - generalization: O_T(n^{−3}) (|h(n)| ≤ C f(n) for n ≥ n_T, p.5) → an explicit C > 0 depending only on T, chosen before G, with the bound for every n ≥ 1; reason: n_T = 1 is a special choice of the threshold; the bound is a nonnegative quantity, so the absolute value is not needed
--   - encoding: Z = L_x(G)(B), its clusters C_v → Zgraph x G B on Fin (v(L_x(G))·B), vertex i in the cluster of vertex i / B; reason: one numbering of the B-blow-up; every quantity involved is isomorphism-invariant
--   - encoding: hom(T, J) for a subgraph J ⊆ Z → homCount T J.coe (homomorphisms into J as a graph on V(J)); reason: the same count: isolated vertices of T are mapped to vertices of J
--   - encoding: sums over Q ∈ 𝒬_T of f_Q(x)·(…) with f_Q a sum over sequences with T_s ≅ Q → sums directly over the sequences of (4.1), grouped by p(T_s); reason: regrouping a finite sum; hom(·,G), v(·), p(·) are isomorphism-invariant, so the values are equal
--   - generalization: v(T) ≥ 3 (the standing assumption of §4, p.12) → every bipartite T with e(T) > 0 (v(T) ≥ 2, s = v(T) − 2 ≥ 0); reason: for v(T) = 2 the construction is L_x(G) = G with the empty sequence; the source's case v(T) ≥ 3 is included
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Lemma 4.8, p.20

import Mathlib
import Definitions.Def_GenTuranHard_A0
import Definitions.Def_GenTuranHard_Zgraph
import Definitions.Def_GenTuranHard_exT

set_option autoImplicit false

namespace GenTuranHard

/-- **Lemma 4.8** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Lemma 4.8, p.20). Let `T`
be bipartite with `e(T) > 0`, `𝓕` a family no member of which is a subgraph of a blow-up of `T`, and
`k = min_{F ∈ 𝓕} χ(F)`. There is a constant `η = η(T, 𝓕) > 0` such that every `𝓕`-free subgraph
`J ⊆ Z = L_x(G)(B)` satisfies
`hom(T, J) ≤ B^{v(T)} (A₀(x, G) + S(x, n)·z + S(x, n)·O(n^{k−η}B^{−η} + n^{−3}))`,
where `z = ex(G, K₂, K_k)`.

**Formalization Note** `k` is encoded by `hkF` and `hkF'`. The paper states the lemma for `G ∈ 𝒢_k`
with `z = cut_{k−1}(G)`, equal to `ex(G, K₂, K_k)` there by (4.9); here `G` is any graph with `n ≥ 1`
and `z = ex(G, K₂, K_k)`. `O(·)` is `C·(·)` with `η, C > 0` depending only on `T, 𝓕`, chosen before
`G`, `B ≥ 1` and `J`. Powers with real exponents are `Real.rpow`. -/
theorem lemma_4_8 {W : Type} [Fintype W] (T : SimpleGraph W) (hT : T.IsBipartite)
    (hTe : T.edgeSet.Nonempty) (Fam : Set FinGraph) (hF : ∀ F ∈ Fam, ¬ InBlowUp F.2 T)
    (k : ℕ) (hkF : ∀ F ∈ Fam, ¬ F.2.Colorable (k - 1)) (hkF' : ∃ F ∈ Fam, F.2.Colorable k) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (G : FinGraph) (B : ℕ), 1 ≤ G.1 → 1 ≤ B →
      ∀ J : (Zgraph (xVec (Fintype.card W) G.1) G B).2.Subgraph, FamFree Fam J.coe →
        (homCount T J.coe : ℝ) ≤ (B : ℝ) ^ Fintype.card W *
          ((A0 T (xVec (Fintype.card W) G.1) G : ℝ) +
            (Sx T (xVec (Fintype.card W) G.1) G.1 : ℝ) *
              (exT G.2 (⊤ : SimpleGraph (Fin 2)) {cliqueFG k} : ℝ) +
            (Sx T (xVec (Fintype.card W) G.1) G.1 : ℝ) *
              (C * ((G.1 : ℝ) ^ ((k : ℝ) - η) * (B : ℝ) ^ (-η) + (G.1 : ℝ) ^ (-3 : ℤ)))) := by sorry

end GenTuranHard
